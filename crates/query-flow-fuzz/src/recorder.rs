//! Event recording and export.

use crate::config::SerializableConfig;
use parking_lot::Mutex;
use query_flow_inspector::{EventSink, ExecutionTrace, FlowEvent};
use serde::{Deserialize, Serialize};
use std::path::Path;
use std::time::Instant;

/// Enhanced event recorder with timestamps.
pub struct FuzzEventRecorder {
    events: Mutex<Vec<TimestampedEvent>>,
    start_time: Instant,
}

impl FuzzEventRecorder {
    pub fn new() -> Self {
        Self {
            events: Mutex::new(Vec::new()),
            start_time: Instant::now(),
        }
    }

    /// Get all recorded events.
    pub fn events(&self) -> Vec<TimestampedEvent> {
        self.events.lock().clone()
    }

    /// Get events as an ExecutionTrace.
    pub fn trace(&self) -> ExecutionTrace {
        ExecutionTrace {
            events: self.events.lock().iter().map(|e| e.event.clone()).collect(),
        }
    }

    /// Take and clear all events.
    pub fn take(&self) -> Vec<TimestampedEvent> {
        std::mem::take(&mut *self.events.lock())
    }

    /// Clear all events.
    pub fn clear(&self) {
        self.events.lock().clear();
    }

    /// Get the number of recorded events.
    pub fn len(&self) -> usize {
        self.events.lock().len()
    }

    /// Check if no events have been recorded.
    pub fn is_empty(&self) -> bool {
        self.events.lock().is_empty()
    }

    /// Export events to a JSON file.
    pub fn export_to_file(&self, path: &Path) -> std::io::Result<()> {
        let events = self.events();
        let json = serde_json::to_string_pretty(&events)?;
        std::fs::write(path, json)
    }
}

impl Default for FuzzEventRecorder {
    fn default() -> Self {
        Self::new()
    }
}

impl EventSink for FuzzEventRecorder {
    fn emit(&self, event: FlowEvent) {
        let timestamp_us = self.start_time.elapsed().as_micros() as u64;
        self.events.lock().push(TimestampedEvent {
            timestamp_us,
            event,
        });
    }

    fn flush(&self) {
        // No-op for now
    }
}

/// Event with timestamp.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimestampedEvent {
    /// Microseconds since test start.
    pub timestamp_us: u64,
    /// The actual event.
    pub event: FlowEvent,
}

/// Complete test run record for export.
#[derive(Debug, Serialize, Deserialize)]
pub struct FuzzRunRecord {
    /// Configuration used.
    pub config: SerializableConfig,
    /// Seed used (for reproducibility).
    pub seed: u64,
    /// All timestamped events.
    pub events: Vec<TimestampedEvent>,
    /// Summary statistics.
    pub stats: RunStats,
    /// Metadata.
    pub metadata: RunMetadata,
}

impl FuzzRunRecord {
    /// Export to a JSON file.
    pub fn export_to_file(&self, path: &Path) -> std::io::Result<()> {
        let json = serde_json::to_string_pretty(self)?;
        std::fs::write(path, json)
    }
}

/// Summary statistics for a test run.
#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub struct RunStats {
    pub total_queries_executed: u64,
    pub cache_hits: u64,
    pub cache_misses: u64,
    pub early_cutoffs: u64,
    pub total_query_time_us: u64,
    pub total_asset_updates: u64,
    pub validation_passes: u64,
    pub validation_failures: u64,
}

impl RunStats {
    /// Compute stats from events and result.
    pub fn from_events(events: &[TimestampedEvent], result: &crate::runner::FuzzResult) -> Self {
        use query_flow_inspector::{ExecutionResult, FlowEvent};

        let mut stats = RunStats::default();

        for event in events {
            match &event.event {
                FlowEvent::QueryEnd {
                    result: exec_result,
                    duration,
                    ..
                } => {
                    stats.total_queries_executed += 1;
                    stats.total_query_time_us += duration.as_micros() as u64;

                    match exec_result {
                        ExecutionResult::CacheHit => stats.cache_hits += 1,
                        ExecutionResult::Changed | ExecutionResult::Unchanged => {
                            stats.cache_misses += 1;
                        }
                        _ => {}
                    }
                }
                FlowEvent::EarlyCutoffCheck {
                    output_changed: false,
                    ..
                } => {
                    stats.early_cutoffs += 1;
                }
                FlowEvent::AssetResolved { .. } => {
                    stats.total_asset_updates += 1;
                }
                _ => {}
            }
        }

        stats.validation_passes = result.validation_successes as u64;
        stats.validation_failures = result.validation_failures.len() as u64;

        stats
    }
}

/// Metadata for a test run.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RunMetadata {
    pub timestamp: String,
    pub duration_ms: u64,
    pub platform: String,
}

impl RunMetadata {
    pub fn new(duration_ms: u64) -> Self {
        Self {
            timestamp: chrono_lite_timestamp(),
            duration_ms,
            platform: std::env::consts::OS.to_string(),
        }
    }
}

/// Simple timestamp without chrono dependency.
fn chrono_lite_timestamp() -> String {
    use std::time::SystemTime;
    let duration = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .unwrap_or_default();
    format!("{}", duration.as_secs())
}
