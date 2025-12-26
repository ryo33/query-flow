//! Tests for the assets system.

use std::sync::atomic::{AtomicU32, Ordering};

use query_flow::{
    asset_key, query, AssetKey, AssetLocator, DurabilityLevel, LoadingState, LocateResult,
    QueryError, QueryRuntime,
};

// ============================================================================
// Test Asset Keys
// ============================================================================

#[asset_key(asset = String)]
pub struct ConfigFile(pub String);

#[asset_key(asset = String, durability = constant)]
pub struct BundledAsset(pub String);

// Use type alias for generic types with angle brackets
type ByteVec = Vec<u8>;

#[asset_key(asset = ByteVec, durability = stable)]
pub struct BinaryFile(pub String);

// ============================================================================
// Test Locators
// ============================================================================

/// Locator that always returns Pending (for async loading).
struct PendingLocator;

impl AssetLocator<ConfigFile> for PendingLocator {
    fn locate(&self, _key: &ConfigFile) -> LocateResult<String> {
        LocateResult::Pending
    }
}

/// Locator that returns Ready immediately.
struct ImmediateLocator {
    content: String,
}

impl AssetLocator<ConfigFile> for ImmediateLocator {
    fn locate(&self, _key: &ConfigFile) -> LocateResult<String> {
        LocateResult::Ready(self.content.clone())
    }
}

/// Locator that returns NotFound.
struct NotFoundLocator;

impl AssetLocator<ConfigFile> for NotFoundLocator {
    fn locate(&self, _key: &ConfigFile) -> LocateResult<String> {
        LocateResult::NotFound
    }
}

// ============================================================================
// Basic Asset Tests
// ============================================================================

#[test]
fn test_asset_key_macro() {
    // Test that the macro generates correct implementations
    let config = ConfigFile("config.json".to_string());
    assert_eq!(config.durability(), DurabilityLevel::Volatile);

    let bundled = BundledAsset("bundle.json".to_string());
    assert_eq!(bundled.durability(), DurabilityLevel::Constant);

    let binary = BinaryFile("data.bin".to_string());
    assert_eq!(binary.durability(), DurabilityLevel::Stable);
}

#[test]
fn test_resolve_asset_before_query() {
    let runtime = QueryRuntime::new();

    // Pre-populate asset before any query
    runtime.resolve_asset(ConfigFile("app.json".to_string()), "config content".to_string());

    // Define a query that uses the asset
    #[query]
    fn read_config(ctx: &mut QueryContext, path: ConfigFile) -> Result<String, QueryError> {
        let content = ctx.asset(path)?.suspend()?;
        Ok((*content).clone())
    }

    // Query should succeed because asset is already resolved
    let result = runtime.query(ReadConfig::new(ConfigFile("app.json".to_string())));
    assert!(result.is_ok());
    assert_eq!(*result.unwrap(), "config content");
}

#[test]
fn test_pending_asset_flow() {
    let runtime = QueryRuntime::new();
    runtime.register_asset_locator::<ConfigFile, _>(PendingLocator);

    #[query]
    fn read_config(ctx: &mut QueryContext, path: ConfigFile) -> Result<String, QueryError> {
        let content = ctx.asset(path)?.suspend()?;
        Ok((*content).clone())
    }

    // First query should suspend
    let result = runtime.query(ReadConfig::new(ConfigFile("app.json".to_string())));
    assert!(matches!(result, Err(QueryError::Suspend)));

    // Check pending assets
    assert!(runtime.has_pending_assets());
    let pending = runtime.pending_assets_of::<ConfigFile>();
    assert_eq!(pending.len(), 1);
    assert_eq!(pending[0].0, "app.json");

    // Resolve the asset
    runtime.resolve_asset(ConfigFile("app.json".to_string()), "resolved content".to_string());

    // Now query should succeed
    let result = runtime.query(ReadConfig::new(ConfigFile("app.json".to_string())));
    assert!(result.is_ok());
    assert_eq!(*result.unwrap(), "resolved content");

    // Pending should be cleared
    assert!(!runtime.has_pending_assets());
}

#[test]
fn test_immediate_locator() {
    let runtime = QueryRuntime::new();
    runtime.register_asset_locator::<ConfigFile, _>(ImmediateLocator {
        content: "immediate content".to_string(),
    });

    #[query]
    fn read_config(ctx: &mut QueryContext, path: ConfigFile) -> Result<String, QueryError> {
        let content = ctx.asset(path)?.suspend()?;
        Ok((*content).clone())
    }

    // Query should succeed immediately
    let result = runtime.query(ReadConfig::new(ConfigFile("any.json".to_string())));
    assert!(result.is_ok());
    assert_eq!(*result.unwrap(), "immediate content");
}

#[test]
fn test_not_found_asset() {
    let runtime = QueryRuntime::new();
    runtime.register_asset_locator::<ConfigFile, _>(NotFoundLocator);

    #[query]
    fn read_config(ctx: &mut QueryContext, path: ConfigFile) -> Result<String, QueryError> {
        let content = ctx.asset(path)?.suspend()?;
        Ok((*content).clone())
    }

    // Query should fail with MissingDependency
    let result = runtime.query(ReadConfig::new(ConfigFile("missing.json".to_string())));
    assert!(matches!(result, Err(QueryError::MissingDependency { .. })));
}

#[test]
fn test_invalidate_asset() {
    let runtime = QueryRuntime::new();

    // Resolve initial value
    runtime.resolve_asset(ConfigFile("app.json".to_string()), "initial".to_string());

    #[query]
    fn read_config(ctx: &mut QueryContext, path: ConfigFile) -> Result<String, QueryError> {
        let content = ctx.asset(path)?.suspend()?;
        Ok((*content).clone())
    }

    // First query returns initial value
    let result = runtime.query(ReadConfig::new(ConfigFile("app.json".to_string())));
    assert_eq!(*result.unwrap(), "initial");

    // Invalidate the asset
    runtime.invalidate_asset(&ConfigFile("app.json".to_string()));

    // Query should now suspend
    let result = runtime.query(ReadConfig::new(ConfigFile("app.json".to_string())));
    assert!(matches!(result, Err(QueryError::Suspend)));

    // Resolve with new value
    runtime.resolve_asset(ConfigFile("app.json".to_string()), "updated".to_string());

    // Query should return new value
    let result = runtime.query(ReadConfig::new(ConfigFile("app.json".to_string())));
    assert_eq!(*result.unwrap(), "updated");
}

#[test]
fn test_asset_caching() {
    static LOCATOR_CALLS: AtomicU32 = AtomicU32::new(0);

    struct CountingLocator;
    impl AssetLocator<ConfigFile> for CountingLocator {
        fn locate(&self, _key: &ConfigFile) -> LocateResult<String> {
            LOCATOR_CALLS.fetch_add(1, Ordering::SeqCst);
            LocateResult::Ready("cached".to_string())
        }
    }

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator::<ConfigFile, _>(CountingLocator);

    #[query]
    fn read_config(ctx: &mut QueryContext, path: ConfigFile) -> Result<String, QueryError> {
        let content = ctx.asset(path)?.suspend()?;
        Ok((*content).clone())
    }

    // First query triggers locator
    LOCATOR_CALLS.store(0, Ordering::SeqCst);
    let _ = runtime.query(ReadConfig::new(ConfigFile("app.json".to_string())));
    assert_eq!(LOCATOR_CALLS.load(Ordering::SeqCst), 1);

    // Second query should use cache, not call locator again
    let _ = runtime.query(ReadConfig::new(ConfigFile("app.json".to_string())));
    assert_eq!(LOCATOR_CALLS.load(Ordering::SeqCst), 1);
}

#[test]
fn test_asset_dependency_tracking() {
    static QUERY_CALLS: AtomicU32 = AtomicU32::new(0);

    let runtime = QueryRuntime::new();
    runtime.resolve_asset(ConfigFile("app.json".to_string()), "v1".to_string());

    #[query]
    fn process_config(ctx: &mut QueryContext, path: ConfigFile) -> Result<String, QueryError> {
        QUERY_CALLS.fetch_add(1, Ordering::SeqCst);
        let content = ctx.asset(path)?.suspend()?;
        Ok(format!("processed: {}", content))
    }

    QUERY_CALLS.store(0, Ordering::SeqCst);

    // First query
    let result = runtime.query(ProcessConfig::new(ConfigFile("app.json".to_string())));
    assert_eq!(*result.unwrap(), "processed: v1");
    assert_eq!(QUERY_CALLS.load(Ordering::SeqCst), 1);

    // Second query - should be cached
    let result = runtime.query(ProcessConfig::new(ConfigFile("app.json".to_string())));
    assert_eq!(*result.unwrap(), "processed: v1");
    assert_eq!(QUERY_CALLS.load(Ordering::SeqCst), 1); // Still 1

    // Update asset - should invalidate dependent query
    runtime.resolve_asset(ConfigFile("app.json".to_string()), "v2".to_string());

    // Query should recompute
    let result = runtime.query(ProcessConfig::new(ConfigFile("app.json".to_string())));
    assert_eq!(*result.unwrap(), "processed: v2");
    assert_eq!(QUERY_CALLS.load(Ordering::SeqCst), 2); // Now 2
}

#[test]
fn test_asset_early_cutoff() {
    static DOWNSTREAM_CALLS: AtomicU32 = AtomicU32::new(0);

    let runtime = QueryRuntime::new();
    runtime.resolve_asset(ConfigFile("app.json".to_string()), "same_value".to_string());

    #[query]
    fn process_config(ctx: &mut QueryContext, path: ConfigFile) -> Result<String, QueryError> {
        DOWNSTREAM_CALLS.fetch_add(1, Ordering::SeqCst);
        let content = ctx.asset(path)?.suspend()?;
        Ok(format!("processed: {}", content))
    }

    DOWNSTREAM_CALLS.store(0, Ordering::SeqCst);

    // First query
    let _ = runtime.query(ProcessConfig::new(ConfigFile("app.json".to_string())));
    assert_eq!(DOWNSTREAM_CALLS.load(Ordering::SeqCst), 1);

    // Resolve with same value - should not trigger recomputation
    runtime.resolve_asset(ConfigFile("app.json".to_string()), "same_value".to_string());

    let _ = runtime.query(ProcessConfig::new(ConfigFile("app.json".to_string())));
    // Early cutoff: same value means no recomputation needed
    assert_eq!(DOWNSTREAM_CALLS.load(Ordering::SeqCst), 1);
}

#[test]
fn test_resolve_asset_with_durability() {
    let runtime = QueryRuntime::new();

    // Resolve with explicit durability
    runtime.resolve_asset_with_durability(
        ConfigFile("config.json".to_string()),
        "content".to_string(),
        DurabilityLevel::Constant,
    );

    #[query]
    fn read_config(ctx: &mut QueryContext, path: ConfigFile) -> Result<String, QueryError> {
        let content = ctx.asset(path)?.suspend()?;
        Ok((*content).clone())
    }

    let result = runtime.query(ReadConfig::new(ConfigFile("config.json".to_string())));
    assert_eq!(*result.unwrap(), "content");
}

#[test]
fn test_remove_asset() {
    let runtime = QueryRuntime::new();
    runtime.register_asset_locator::<ConfigFile, _>(ImmediateLocator {
        content: "from_locator".to_string(),
    });

    // Pre-resolve asset
    runtime.resolve_asset(ConfigFile("app.json".to_string()), "pre_resolved".to_string());

    #[query]
    fn read_config(ctx: &mut QueryContext, path: ConfigFile) -> Result<String, QueryError> {
        let content = ctx.asset(path)?.suspend()?;
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

    runtime.resolve_asset(ConfigFile("config.json".to_string()), "config content".to_string());
    runtime.resolve_asset(BinaryFile("data.bin".to_string()), vec![1, 2, 3, 4]);

    #[query]
    fn process_files(
        ctx: &mut QueryContext,
        config_path: ConfigFile,
        binary_path: BinaryFile,
    ) -> Result<(String, usize), QueryError> {
        let config = ctx.asset(config_path)?.suspend()?;
        let binary = ctx.asset(binary_path)?.suspend()?;
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
fn test_loading_state_methods() {
    let loading: LoadingState<String> = LoadingState::Loading;
    assert!(loading.is_loading());
    assert!(!loading.is_ready());
    assert!(loading.get().is_none());
    assert!(loading.suspend().is_err());

    let ready: LoadingState<String> = LoadingState::Ready("value".to_string());
    assert!(!ready.is_loading());
    assert!(ready.is_ready());
    assert_eq!(ready.get(), Some(&"value".to_string()));
    assert_eq!(ready.suspend().unwrap(), "value");
}

#[test]
fn test_no_locator_pending() {
    let runtime = QueryRuntime::new();
    // No locator registered

    #[query]
    fn read_config(ctx: &mut QueryContext, path: ConfigFile) -> Result<String, QueryError> {
        let content = ctx.asset(path)?.suspend()?;
        Ok((*content).clone())
    }

    // Without a locator, asset should be marked as pending
    let result = runtime.query(ReadConfig::new(ConfigFile("app.json".to_string())));
    assert!(matches!(result, Err(QueryError::Suspend)));

    // Check that it's in pending
    assert!(runtime.has_pending_assets());
    let pending = runtime.pending_assets_of::<ConfigFile>();
    assert_eq!(pending.len(), 1);
}
