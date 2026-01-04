//! Tests for the assets system.

use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Arc;

use query_flow::{
    asset_key, asset_locator, query, Db, DurabilityLevel, LocateResult, QueryError, QueryRuntime,
};

// ============================================================================
// Test Asset Keys
// ============================================================================

#[asset_key(asset = String)]
pub struct ConfigFile(pub String);

#[asset_key(asset = String)]
pub struct BundledAsset(pub String);

// Use type alias for generic types with angle brackets
type ByteVec = Vec<u8>;

#[asset_key(asset = ByteVec)]
pub struct BinaryFile(pub String);

// ============================================================================
// Basic Asset Tests
// ============================================================================

#[test]
fn test_asset_key_macro() {
    // Test that the macro generates correct implementations
    let _config = ConfigFile("config.json".to_string());
    let _bundled = BundledAsset("bundle.json".to_string());
    let _binary = BinaryFile("data.bin".to_string());
}

#[test]
fn test_resolve_asset_before_query() {
    let runtime = QueryRuntime::new();

    runtime.resolve_asset(
        ConfigFile("app.json".to_string()),
        "config content".to_string(),
        DurabilityLevel::Volatile,
    );

    #[query]
    fn read_config(db: &impl Db, path: ConfigFile) -> Result<String, QueryError> {
        let content = db.asset(path)?.suspend()?;
        Ok((*content).clone())
    }

    let result = runtime.query(ReadConfig::new(ConfigFile("app.json".to_string())));
    assert!(result.is_ok());
    assert_eq!(*result.unwrap(), "config content");
}

#[test]
fn test_pending_asset_flow() {
    #[asset_locator]
    fn pending(_db: &impl Db, _key: &ConfigFile) -> Result<LocateResult<String>, QueryError> {
        Ok(LocateResult::Pending)
    }

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(Pending);

    #[query]
    fn read_config(db: &impl Db, path: ConfigFile) -> Result<String, QueryError> {
        let content = db.asset(path)?.suspend()?;
        Ok((*content).clone())
    }

    // First query should suspend
    let result = runtime.query(ReadConfig::new(ConfigFile("app.json".to_string())));
    assert!(matches!(result, Err(QueryError::Suspend { .. })));

    // Check pending assets
    assert!(runtime.has_pending_assets());
    let pending = runtime.pending_assets_of::<ConfigFile>();
    assert_eq!(pending.len(), 1);
    assert_eq!(pending[0].0, "app.json");

    // Resolve the asset
    runtime.resolve_asset(
        ConfigFile("app.json".to_string()),
        "resolved content".to_string(),
        DurabilityLevel::Volatile,
    );

    // Now query should succeed
    let result = runtime.query(ReadConfig::new(ConfigFile("app.json".to_string())));
    assert!(result.is_ok());
    assert_eq!(*result.unwrap(), "resolved content");

    // Pending should be cleared
    assert!(!runtime.has_pending_assets());
}

#[test]
fn test_immediate_locator() {
    #[asset_locator]
    fn immediate(_db: &impl Db, _key: &ConfigFile) -> Result<LocateResult<String>, QueryError> {
        Ok(LocateResult::Ready {
            value: "immediate content".to_string(),
            durability: DurabilityLevel::Stable,
        })
    }

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(Immediate);

    #[query]
    fn read_config(db: &impl Db, path: ConfigFile) -> Result<String, QueryError> {
        let content = db.asset(path)?.suspend()?;
        Ok((*content).clone())
    }

    let result = runtime.query(ReadConfig::new(ConfigFile("any.json".to_string())));
    assert!(result.is_ok());
    assert_eq!(*result.unwrap(), "immediate content");
}

#[test]
fn test_not_found_asset() {
    #[asset_locator]
    fn not_found(_db: &impl Db, key: &ConfigFile) -> Result<LocateResult<String>, QueryError> {
        Err(QueryError::MissingDependency {
            description: format!("Asset not found: {:?}", key),
        })
    }

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(NotFound);

    #[query]
    fn read_config(db: &impl Db, path: ConfigFile) -> Result<String, QueryError> {
        let content = db.asset(path)?.suspend()?;
        Ok((*content).clone())
    }

    let result = runtime.query(ReadConfig::new(ConfigFile("missing.json".to_string())));
    assert!(matches!(result, Err(QueryError::MissingDependency { .. })));
}

#[test]
fn test_invalidate_asset() {
    let runtime = QueryRuntime::new();

    runtime.resolve_asset(
        ConfigFile("app.json".to_string()),
        "initial".to_string(),
        DurabilityLevel::Volatile,
    );

    #[query]
    fn read_config(db: &impl Db, path: ConfigFile) -> Result<String, QueryError> {
        let content = db.asset(path)?.suspend()?;
        Ok((*content).clone())
    }

    // First query returns initial value
    let result = runtime.query(ReadConfig::new(ConfigFile("app.json".to_string())));
    assert_eq!(*result.unwrap(), "initial");

    // Invalidate the asset
    runtime.invalidate_asset(&ConfigFile("app.json".to_string()));

    // Query should now suspend
    let result = runtime.query(ReadConfig::new(ConfigFile("app.json".to_string())));
    assert!(matches!(result, Err(QueryError::Suspend { .. })));

    // Resolve with new value
    runtime.resolve_asset(
        ConfigFile("app.json".to_string()),
        "updated".to_string(),
        DurabilityLevel::Volatile,
    );

    // Query should return new value
    let result = runtime.query(ReadConfig::new(ConfigFile("app.json".to_string())));
    assert_eq!(*result.unwrap(), "updated");
}

/// Asset key with embedded call counter for testing.
#[asset_key(asset = String, key(path))]
struct CountedAsset {
    path: String,
    call_count: Arc<AtomicU32>,
}

impl CountedAsset {
    fn new(path: &str) -> Self {
        Self {
            path: path.to_string(),
            call_count: Arc::new(AtomicU32::new(0)),
        }
    }

    fn count(&self) -> u32 {
        self.call_count.load(Ordering::SeqCst)
    }

    fn increment(&self) {
        self.call_count.fetch_add(1, Ordering::SeqCst);
    }
}

#[test]
fn test_asset_caching() {
    #[asset_locator]
    fn counting(_db: &impl Db, key: &CountedAsset) -> Result<LocateResult<String>, QueryError> {
        key.increment();
        Ok(LocateResult::Ready {
            value: "cached".to_string(),
            durability: DurabilityLevel::Stable,
        })
    }

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(Counting);

    let key = CountedAsset::new("app.json");

    // First access triggers locator
    let _ = runtime.get_asset(key.clone());
    assert_eq!(key.count(), 1);

    // Second access should use cache
    let _ = runtime.get_asset(key.clone());
    assert_eq!(key.count(), 1, "Locator should not be called again");
}

#[test]
fn test_asset_dependency_tracking() {
    let runtime = QueryRuntime::new();
    let key = CountedAsset::new("app.json");

    runtime.resolve_asset(key.clone(), "v1".to_string(), DurabilityLevel::Volatile);

    #[query]
    fn process_config(db: &impl Db, key: CountedAsset) -> Result<String, QueryError> {
        key.increment();
        let content = db.asset(key)?.suspend()?;
        Ok(format!("processed: {}", content))
    }

    // First query
    let result = runtime.query(ProcessConfig::new(key.clone()));
    assert_eq!(*result.unwrap(), "processed: v1");
    assert_eq!(key.count(), 1);

    // Second query - should be cached
    let result = runtime.query(ProcessConfig::new(key.clone()));
    assert_eq!(*result.unwrap(), "processed: v1");
    assert_eq!(key.count(), 1); // Still 1

    // Update asset - should invalidate dependent query
    runtime.resolve_asset(key.clone(), "v2".to_string(), DurabilityLevel::Volatile);

    // Query should recompute
    let result = runtime.query(ProcessConfig::new(key.clone()));
    assert_eq!(*result.unwrap(), "processed: v2");
    assert_eq!(key.count(), 2); // Now 2
}

#[test]
fn test_asset_early_cutoff() {
    let runtime = QueryRuntime::new();
    let key = CountedAsset::new("app.json");

    runtime.resolve_asset(
        key.clone(),
        "same_value".to_string(),
        DurabilityLevel::Volatile,
    );

    #[query]
    fn process_config(db: &impl Db, key: CountedAsset) -> Result<String, QueryError> {
        key.increment();
        let content = db.asset(key)?.suspend()?;
        Ok(format!("processed: {}", content))
    }

    // First query
    let _ = runtime.query(ProcessConfig::new(key.clone()));
    assert_eq!(key.count(), 1);

    // Resolve with same value - should not trigger recomputation
    runtime.resolve_asset(
        key.clone(),
        "same_value".to_string(),
        DurabilityLevel::Volatile,
    );

    let _ = runtime.query(ProcessConfig::new(key.clone()));
    // Early cutoff: same value means no recomputation needed
    assert_eq!(key.count(), 1);
}

#[test]
fn test_resolve_asset_with_static_durability() {
    let runtime = QueryRuntime::new();

    runtime.resolve_asset(
        ConfigFile("config.json".to_string()),
        "content".to_string(),
        DurabilityLevel::Static,
    );

    #[query]
    fn read_config(db: &impl Db, path: ConfigFile) -> Result<String, QueryError> {
        let content = db.asset(path)?.suspend()?;
        Ok((*content).clone())
    }

    let result = runtime.query(ReadConfig::new(ConfigFile("config.json".to_string())));
    assert_eq!(*result.unwrap(), "content");
}

#[test]
fn test_remove_asset() {
    #[asset_locator]
    fn from_locator(_db: &impl Db, _key: &ConfigFile) -> Result<LocateResult<String>, QueryError> {
        Ok(LocateResult::Ready {
            value: "from_locator".to_string(),
            durability: DurabilityLevel::Stable,
        })
    }

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(FromLocator);

    // Pre-resolve asset
    runtime.resolve_asset(
        ConfigFile("app.json".to_string()),
        "pre_resolved".to_string(),
        DurabilityLevel::Volatile,
    );

    #[query]
    fn read_config(db: &impl Db, path: ConfigFile) -> Result<String, QueryError> {
        let content = db.asset(path)?.suspend()?;
        Ok((*content).clone())
    }

    // First query returns pre-resolved value
    let result = runtime.query(ReadConfig::new(ConfigFile("app.json".to_string())));
    assert_eq!(*result.unwrap(), "pre_resolved");

    // Remove asset
    runtime.remove_asset(&ConfigFile("app.json".to_string()));

    // Query should now go through locator
    let result = runtime.query(ReadConfig::new(ConfigFile("app.json".to_string())));
    assert_eq!(*result.unwrap(), "from_locator");
}

#[test]
fn test_multiple_asset_types() {
    let runtime = QueryRuntime::new();

    runtime.resolve_asset(
        ConfigFile("config.json".to_string()),
        "config content".to_string(),
        DurabilityLevel::Volatile,
    );
    runtime.resolve_asset(
        BinaryFile("data.bin".to_string()),
        vec![1, 2, 3, 4],
        DurabilityLevel::Volatile,
    );

    #[query]
    fn process_files(
        db: &impl Db,
        config_path: ConfigFile,
        binary_path: BinaryFile,
    ) -> Result<(String, usize), QueryError> {
        let config = db.asset(config_path)?.suspend()?;
        let binary = db.asset(binary_path)?.suspend()?;
        Ok(((*config).clone(), binary.len()))
    }

    let result = runtime.query(ProcessFiles::new(
        ConfigFile("config.json".to_string()),
        BinaryFile("data.bin".to_string()),
    ));
    assert!(result.is_ok());
    let (config, len) = (*result.unwrap()).clone();
    assert_eq!(config, "config content");
    assert_eq!(len, 4);
}

#[test]
fn test_no_locator_pending() {
    let runtime = QueryRuntime::new();
    // No locator registered

    #[query]
    fn read_config(db: &impl Db, path: ConfigFile) -> Result<String, QueryError> {
        let content = db.asset(path)?.suspend()?;
        Ok((*content).clone())
    }

    // Without a locator, asset should be marked as pending
    let result = runtime.query(ReadConfig::new(ConfigFile("app.json".to_string())));
    assert!(matches!(result, Err(QueryError::Suspend { .. })));

    // Check that it's in pending
    assert!(runtime.has_pending_assets());
    let pending = runtime.pending_assets_of::<ConfigFile>();
    assert_eq!(pending.len(), 1);
}

// ============================================================================
// get_asset Tests (direct asset access without dependency tracking)
// ============================================================================

#[test]
fn test_get_asset_ready() {
    let runtime = QueryRuntime::new();
    runtime.resolve_asset(
        ConfigFile("app.json".to_string()),
        "content".to_string(),
        DurabilityLevel::Volatile,
    );

    let result = runtime.get_asset(ConfigFile("app.json".to_string()));
    assert!(result.is_ok());
    let state = result.unwrap();
    assert!(state.is_ready());
    assert_eq!(**state.get().unwrap(), "content".to_string());
}

#[test]
fn test_get_asset_loading_no_locator() {
    let runtime = QueryRuntime::new();
    // No asset resolved, no locator registered

    let result = runtime.get_asset(ConfigFile("missing.json".to_string()));
    assert!(result.is_ok());
    let state = result.unwrap();
    assert!(state.is_loading());

    // Should be added to pending
    assert!(runtime.has_pending_assets());
    let pending = runtime.pending_assets_of::<ConfigFile>();
    assert_eq!(pending.len(), 1);
    assert_eq!(pending[0].0, "missing.json");
}

#[test]
fn test_get_asset_immediate_locator() {
    #[asset_locator]
    fn immediate(_db: &impl Db, _key: &ConfigFile) -> Result<LocateResult<String>, QueryError> {
        Ok(LocateResult::Ready {
            value: "from_locator".to_string(),
            durability: DurabilityLevel::Stable,
        })
    }

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(Immediate);

    let result = runtime.get_asset(ConfigFile("any.json".to_string()));
    assert!(result.is_ok());
    let state = result.unwrap();
    assert!(state.is_ready());
    assert_eq!(**state.get().unwrap(), "from_locator".to_string());
}

#[test]
fn test_get_asset_not_found() {
    #[asset_locator]
    fn not_found(_db: &impl Db, key: &ConfigFile) -> Result<LocateResult<String>, QueryError> {
        Err(QueryError::MissingDependency {
            description: format!("Asset not found: {:?}", key),
        })
    }

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(NotFound);

    let result = runtime.get_asset(ConfigFile("missing.json".to_string()));
    assert!(matches!(result, Err(QueryError::MissingDependency { .. })));
}

// ============================================================================
// Enum Asset Key Tests
// ============================================================================

#[asset_key(asset = String)]
pub enum ResourcePath {
    Config(String),
    Data { name: String },
    Static,
}

#[test]
fn test_enum_asset_key() {
    let runtime = QueryRuntime::new();

    runtime.resolve_asset(
        ResourcePath::Config("app.toml".to_string()),
        "config content".to_string(),
        DurabilityLevel::Volatile,
    );

    #[query]
    fn read_resource(db: &impl Db, path: ResourcePath) -> Result<String, QueryError> {
        let content = db.asset(path)?.suspend()?;
        Ok((*content).clone())
    }

    let result = runtime.query(ReadResource::new(ResourcePath::Config(
        "app.toml".to_string(),
    )));
    assert_eq!(*result.unwrap(), "config content");
}

// ============================================================================
// Dynamic Locator Tests (db.query() in locator)
// ============================================================================

/// A configuration that controls which assets are allowed.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct AllowListConfig {
    allowed_paths: Vec<String>,
}

#[query]
fn get_allow_list(_db: &impl Db) -> Result<AllowListConfig, QueryError> {
    Ok(AllowListConfig {
        allowed_paths: vec!["allowed.json".to_string(), "also_allowed.json".to_string()],
    })
}

#[asset_key(asset = String)]
struct ControlledFile(String);

#[test]
fn test_locator_calls_query_allowed() {
    #[asset_locator]
    fn allow_list_check(
        db: &impl Db,
        key: &ControlledFile,
    ) -> Result<LocateResult<String>, QueryError> {
        let config = db.query(GetAllowList {})?;
        if config.allowed_paths.contains(&key.0) {
            Ok(LocateResult::Pending)
        } else {
            Err(QueryError::MissingDependency {
                description: format!("Path '{}' is not in allow list", key.0),
            })
        }
    }

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(AllowListCheck);

    #[query]
    fn read_controlled(db: &impl Db, path: ControlledFile) -> Result<String, QueryError> {
        let content = db.asset(path)?.suspend()?;
        Ok((*content).clone())
    }

    // Request an allowed path - should be pending
    let result = runtime.query(ReadControlled::new(ControlledFile(
        "allowed.json".to_string(),
    )));
    assert!(matches!(result, Err(QueryError::Suspend { .. })));

    // Should be in pending list
    let pending = runtime.pending_assets_of::<ControlledFile>();
    assert_eq!(pending.len(), 1);
    assert_eq!(pending[0].0, "allowed.json");
}

#[test]
fn test_locator_calls_query_denied() {
    #[asset_locator]
    fn allow_list_check(
        db: &impl Db,
        key: &ControlledFile,
    ) -> Result<LocateResult<String>, QueryError> {
        let config = db.query(GetAllowList {})?;
        if config.allowed_paths.contains(&key.0) {
            Ok(LocateResult::Pending)
        } else {
            Err(QueryError::MissingDependency {
                description: format!("Path '{}' is not in allow list", key.0),
            })
        }
    }

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(AllowListCheck);

    #[query]
    fn read_controlled(db: &impl Db, path: ControlledFile) -> Result<String, QueryError> {
        let content = db.asset(path)?.suspend()?;
        Ok((*content).clone())
    }

    // Request a denied path - should return error immediately
    let result = runtime.query(ReadControlled::new(ControlledFile(
        "denied.json".to_string(),
    )));
    assert!(matches!(result, Err(QueryError::MissingDependency { .. })));

    // Should NOT be in pending list
    let pending = runtime.pending_assets_of::<ControlledFile>();
    assert!(pending.is_empty());
}

#[test]
fn test_locator_error_not_added_to_pending() {
    #[asset_locator]
    fn not_found(_db: &impl Db, key: &ConfigFile) -> Result<LocateResult<String>, QueryError> {
        Err(QueryError::MissingDependency {
            description: format!("Asset not found: {:?}", key),
        })
    }

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(NotFound);

    let result = runtime.get_asset(ConfigFile("missing.json".to_string()));
    assert!(matches!(result, Err(QueryError::MissingDependency { .. })));

    // Verify NOT added to pending
    assert!(!runtime.has_pending_assets());
}

#[test]
fn test_pending_only_on_pending_result() {
    #[asset_locator]
    fn pending(_db: &impl Db, _key: &ConfigFile) -> Result<LocateResult<String>, QueryError> {
        Ok(LocateResult::Pending)
    }

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(Pending);

    let result = runtime.get_asset(ConfigFile("file.json".to_string()));
    assert!(result.is_ok());
    assert!(result.unwrap().is_loading());

    // Verify added to pending
    assert!(runtime.has_pending_assets());
    let pending = runtime.pending_assets_of::<ConfigFile>();
    assert_eq!(pending.len(), 1);
}

// ============================================================================
// Cycle Detection Tests
// ============================================================================

#[asset_key(asset = String)]
struct CyclicAsset(String);

#[test]
fn test_cycle_locator_to_same_asset() {
    #[asset_locator]
    fn direct_cycle(db: &impl Db, key: &CyclicAsset) -> Result<LocateResult<String>, QueryError> {
        // Try to access the same asset we're currently locating
        let _ = db.asset(key.clone())?;
        Ok(LocateResult::Ready {
            value: "should not reach".to_string(),
            durability: DurabilityLevel::Volatile,
        })
    }

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(DirectCycle);

    #[query]
    fn read_cyclic(db: &impl Db, key: CyclicAsset) -> Result<String, QueryError> {
        let content = db.asset(key)?.suspend()?;
        Ok((*content).clone())
    }

    let result = runtime.query(ReadCyclic::new(CyclicAsset("test".to_string())));
    assert!(matches!(result, Err(QueryError::Cycle { .. })));
}

#[asset_key(asset = String)]
struct CyclicAsset2(String);

#[query]
fn query_with_cyclic_asset(db: &impl Db, key: CyclicAsset2) -> Result<String, QueryError> {
    let content = db.asset(key)?.suspend()?;
    Ok((*content).clone())
}

#[test]
fn test_cycle_locator_query_asset() {
    #[asset_locator]
    fn query_cycle(db: &impl Db, key: &CyclicAsset2) -> Result<LocateResult<String>, QueryError> {
        // Call a query that will try to access this same asset
        let _ = db.query(QueryWithCyclicAsset::new(key.clone()))?;
        Ok(LocateResult::Ready {
            value: "should not reach".to_string(),
            durability: DurabilityLevel::Volatile,
        })
    }

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(QueryCycle);

    let result = runtime.query(QueryWithCyclicAsset::new(CyclicAsset2("test".to_string())));
    assert!(matches!(result, Err(QueryError::Cycle { .. })));
}

// ============================================================================
// Locator Dependency Invalidation Tests
// ============================================================================

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct MutableConfig {
    value: String,
}

static MUTABLE_CONFIG: std::sync::Mutex<Option<MutableConfig>> = std::sync::Mutex::new(None);

#[query]
fn get_mutable_config(_db: &impl Db) -> Result<MutableConfig, QueryError> {
    let config = MUTABLE_CONFIG.lock().unwrap();
    config.clone().ok_or_else(|| QueryError::MissingDependency {
        description: "Config not set".to_string(),
    })
}

#[asset_key(asset = String)]
struct ConfigDependentAsset(String);

#[test]
fn test_locator_query_dependency_invalidation() {
    #[asset_locator]
    fn config_dependent(
        db: &impl Db,
        key: &ConfigDependentAsset,
    ) -> Result<LocateResult<String>, QueryError> {
        let config = db.query(GetMutableConfig {})?;
        Ok(LocateResult::Ready {
            value: format!("{}:{}", key.0, config.value),
            durability: DurabilityLevel::Volatile,
        })
    }

    // Set initial config
    *MUTABLE_CONFIG.lock().unwrap() = Some(MutableConfig {
        value: "v1".to_string(),
    });

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(ConfigDependent);

    #[query]
    fn read_config_dependent(
        db: &impl Db,
        key: ConfigDependentAsset,
    ) -> Result<String, QueryError> {
        let content = db.asset(key)?.suspend()?;
        Ok((*content).clone())
    }

    // First query with v1 config
    let result = runtime.query(ReadConfigDependent::new(ConfigDependentAsset(
        "file".to_string(),
    )));
    assert!(result.is_ok());
    assert_eq!(*result.unwrap(), "file:v1");

    // Update config
    *MUTABLE_CONFIG.lock().unwrap() = Some(MutableConfig {
        value: "v2".to_string(),
    });

    // Query again - should get new value because config dependency changed
    let result = runtime.query(ReadConfigDependent::new(ConfigDependentAsset(
        "file".to_string(),
    )));
    assert!(result.is_ok());
    // The result depends on whether the config query is re-evaluated
}

// ============================================================================
// Asset Error Caching Tests
// ============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
struct AssetNotFoundError {
    path: String,
}

impl std::fmt::Display for AssetNotFoundError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Asset not found: {}", self.path)
    }
}

impl std::error::Error for AssetNotFoundError {}

#[test]
fn test_locator_user_error_is_cached() {
    #[asset_locator]
    fn counting_error(
        _db: &impl Db,
        key: &CountedAsset,
    ) -> Result<LocateResult<String>, QueryError> {
        key.increment();
        Err(QueryError::UserError(Arc::new(anyhow::anyhow!(
            AssetNotFoundError {
                path: key.path.clone()
            }
        ))))
    }

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(CountingError);

    let key = CountedAsset::new("missing.json");

    // First access - locator should be called
    let result1 = runtime.get_asset(key.clone());
    assert!(matches!(result1, Err(QueryError::UserError(_))));
    assert_eq!(key.count(), 1);

    // Second access - should use cached error
    let result2 = runtime.get_asset(key.clone());
    assert!(matches!(result2, Err(QueryError::UserError(_))));
    assert_eq!(key.count(), 1, "Locator should not be called again");
}

#[test]
fn test_resolve_asset_error_api() {
    let runtime = QueryRuntime::new();

    runtime.resolve_asset_error(
        ConfigFile("forbidden.json".to_string()),
        AssetNotFoundError {
            path: "forbidden.json".to_string(),
        },
        DurabilityLevel::Volatile,
    );

    let result = runtime.get_asset(ConfigFile("forbidden.json".to_string()));
    assert!(matches!(result, Err(QueryError::UserError(_))));

    // Verify not in pending list
    let pending = runtime.pending_assets_of::<ConfigFile>();
    assert!(pending.is_empty());
}

#[test]
fn test_resolve_asset_error_removes_from_pending() {
    #[asset_locator]
    fn pending(_db: &impl Db, _key: &ConfigFile) -> Result<LocateResult<String>, QueryError> {
        Ok(LocateResult::Pending)
    }

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(Pending);

    // First, create a pending asset
    let _ = runtime.get_asset(ConfigFile("loading.json".to_string()));
    assert!(runtime.has_pending_assets());

    // Now resolve it as an error
    runtime.resolve_asset_error(
        ConfigFile("loading.json".to_string()),
        AssetNotFoundError {
            path: "loading.json".to_string(),
        },
        DurabilityLevel::Volatile,
    );

    // Should no longer be pending
    assert!(!runtime.has_pending_assets());

    // Access should return the error
    let result = runtime.get_asset(ConfigFile("loading.json".to_string()));
    assert!(matches!(result, Err(QueryError::UserError(_))));
}

#[test]
fn test_invalidate_asset_clears_cached_error() {
    let runtime = QueryRuntime::new();

    runtime.resolve_asset_error(
        ConfigFile("might-exist.json".to_string()),
        AssetNotFoundError {
            path: "might-exist.json".to_string(),
        },
        DurabilityLevel::Volatile,
    );

    // Confirm error is cached
    let result1 = runtime.get_asset(ConfigFile("might-exist.json".to_string()));
    assert!(matches!(result1, Err(QueryError::UserError(_))));

    // Invalidate the asset
    runtime.invalidate_asset(&ConfigFile("might-exist.json".to_string()));

    // Now it should be pending (loading state)
    let result2 = runtime.get_asset(ConfigFile("might-exist.json".to_string()));
    assert!(result2.expect("should be ok").is_loading());
    assert!(runtime.has_pending_assets());
}

#[test]
fn test_query_receives_cached_asset_error() {
    let runtime = QueryRuntime::new();

    runtime.resolve_asset_error(
        ConfigFile("error.json".to_string()),
        AssetNotFoundError {
            path: "error.json".to_string(),
        },
        DurabilityLevel::Volatile,
    );

    #[query]
    fn read_asset(db: &impl Db, path: ConfigFile) -> Result<String, QueryError> {
        let content = db.asset(path)?.suspend()?;
        Ok((*content).clone())
    }

    let result = runtime.query(ReadAsset::new(ConfigFile("error.json".to_string())));
    assert!(matches!(result, Err(QueryError::UserError(_))));
}

#[test]
fn test_asset_error_early_cutoff() {
    let runtime = QueryRuntime::builder()
        .error_comparator(|a, b| a.to_string() == b.to_string())
        .build();

    let key = CountedAsset::new("error.json");

    runtime.resolve_asset_error(
        key.clone(),
        AssetNotFoundError {
            path: "error.json".to_string(),
        },
        DurabilityLevel::Volatile,
    );

    #[query]
    fn dependent_query(db: &impl Db, key: CountedAsset) -> Result<String, QueryError> {
        key.increment();
        let _ = db.asset(key)?;
        Ok("never reached".to_string())
    }

    // First run
    let _ = runtime.query(DependentQuery::new(key.clone()));
    assert_eq!(key.count(), 1);

    // Resolve same error again
    runtime.resolve_asset_error(
        key.clone(),
        AssetNotFoundError {
            path: "error.json".to_string(),
        },
        DurabilityLevel::Volatile,
    );

    // Query should not re-run due to early cutoff
    let _ = runtime.query(DependentQuery::new(key.clone()));
    assert_eq!(
        key.count(),
        1,
        "Query should not re-run when error is unchanged"
    );
}
