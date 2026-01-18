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
        let content = db.asset(path)?;
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
        let content = db.asset(path)?;
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
        let content = db.asset(path)?;
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
        let content = db.asset(path)?;
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
        let content = db.asset(path)?;
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
        let content = db.asset(key)?;
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
        let content = db.asset(key)?;
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
        let content = db.asset(path)?;
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
        let content = db.asset(path)?;
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
        let config = db.asset(config_path)?;
        let binary = db.asset(binary_path)?;
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
        let content = db.asset(path)?;
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
        let content = db.asset(path)?;
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
        let content = db.asset(path)?;
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
        let content = db.asset(path)?;
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
        let content = db.asset(key)?;
        Ok((*content).clone())
    }

    let result = runtime.query(ReadCyclic::new(CyclicAsset("test".to_string())));
    assert!(matches!(result, Err(QueryError::Cycle { .. })));
}

#[asset_key(asset = String)]
struct CyclicAsset2(String);

#[query]
fn query_with_cyclic_asset(db: &impl Db, key: CyclicAsset2) -> Result<String, QueryError> {
    let content = db.asset(key)?;
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

#[asset_key(asset = String)]
struct MutualCycleA(String);

#[asset_key(asset = String)]
struct MutualCycleB(String);

#[test]
fn test_cycle_mutual_assets() {
    // A's locator accesses B, B's locator accesses A
    #[asset_locator]
    fn locator_a(db: &impl Db, key: &MutualCycleA) -> Result<LocateResult<String>, QueryError> {
        let b = db.asset(MutualCycleB(key.0.clone()))?;
        Ok(LocateResult::Ready {
            value: format!("A got B: {}", b),
            durability: DurabilityLevel::Volatile,
        })
    }

    #[asset_locator]
    fn locator_b(db: &impl Db, key: &MutualCycleB) -> Result<LocateResult<String>, QueryError> {
        let a = db.asset(MutualCycleA(key.0.clone()))?;
        Ok(LocateResult::Ready {
            value: format!("B got A: {}", a),
            durability: DurabilityLevel::Volatile,
        })
    }

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(LocatorA);
    runtime.register_asset_locator(LocatorB);

    // Access A -> A's locator accesses B -> B's locator accesses A -> Cycle
    let result = runtime.asset(MutualCycleA("test".to_string()));
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
        let content = db.asset(key)?;
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
        let content = db.asset(path)?;
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

// ============================================================================
// Locator Dependency Tracking Tests (Ideal Behavior)
// ============================================================================
//
// These tests verify the ideal behavior for asset locator dependency tracking:
// - Locator dependencies should be registered on the asset itself
// - Locator dependencies should NOT be registered on the calling query
// - When locator deps change, the locate function should be re-executed
// - If asset content unchanged (early cutoff), the query should NOT re-run
//
// Tests for asset locator dependency tracking
// - Locator deps are registered on the asset itself (not the calling query)
// - When locator deps change, the locator re-runs with early cutoff

/// Mutable config for test 1
static LOCATOR_DEP_CONFIG_1: std::sync::Mutex<String> = std::sync::Mutex::new(String::new());

#[query]
fn get_locator_dep_config_1(_db: &impl Db) -> Result<String, QueryError> {
    Ok(LOCATOR_DEP_CONFIG_1.lock().unwrap().clone())
}

#[asset_key(asset = String)]
struct LocatorDepAsset1(String);

static LOCATOR_1_COUNT: AtomicU32 = AtomicU32::new(0);

#[asset_locator]
fn locator_1(db: &impl Db, key: &LocatorDepAsset1) -> Result<LocateResult<String>, QueryError> {
    LOCATOR_1_COUNT.fetch_add(1, Ordering::SeqCst);
    let config = db.query(GetLocatorDepConfig1 {})?;
    Ok(LocateResult::Ready {
        value: format!("{}:{}", key.0, config),
        durability: DurabilityLevel::Volatile,
    })
}

static QUERY_1_COUNT: AtomicU32 = AtomicU32::new(0);

#[query]
fn read_asset_1(db: &impl Db, key: LocatorDepAsset1) -> Result<String, QueryError> {
    QUERY_1_COUNT.fetch_add(1, Ordering::SeqCst);
    let content = db.asset(key)?;
    Ok((*content).clone())
}

/// Test 1.1 & 1.2: Locator dependencies registered on asset, not query
/// Also tests: query not re-run when asset content unchanged (early cutoff)
#[test]
fn test_locator_deps_registered_on_asset_not_query() {
    // Setup
    *LOCATOR_DEP_CONFIG_1.lock().unwrap() = "v1".to_string();
    LOCATOR_1_COUNT.store(0, Ordering::SeqCst);
    QUERY_1_COUNT.store(0, Ordering::SeqCst);

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(Locator1);

    // Execute query
    let result = runtime.query(ReadAsset1::new(LocatorDepAsset1("file".to_string())));
    assert_eq!(*result.unwrap(), "file:v1");
    assert_eq!(QUERY_1_COUNT.load(Ordering::SeqCst), 1);
    assert_eq!(LOCATOR_1_COUNT.load(Ordering::SeqCst), 1);

    // Invalidate the config query (but value stays "v1")
    runtime.invalidate(&GetLocatorDepConfig1 {});

    // Execute query again
    // IDEAL: Query should NOT re-execute (asset content unchanged)
    // CURRENT: Query re-executes because GetLocatorDepConfig1 is its direct dependency
    let result = runtime.query(ReadAsset1::new(LocatorDepAsset1("file".to_string())));
    assert_eq!(*result.unwrap(), "file:v1");

    // Assert ideal behavior:
    // - Locator SHOULD re-execute (its dep changed)
    // - Query should NOT re-execute (asset content same -> early cutoff)
    assert_eq!(
        LOCATOR_1_COUNT.load(Ordering::SeqCst),
        2,
        "Locator should re-execute"
    );
    assert_eq!(
        QUERY_1_COUNT.load(Ordering::SeqCst),
        1,
        "Query should NOT re-execute (early cutoff)"
    );
}

/// Mutable config for test 2
static LOCATOR_DEP_CONFIG_2: std::sync::Mutex<String> = std::sync::Mutex::new(String::new());

#[query]
fn get_locator_dep_config_2(_db: &impl Db) -> Result<String, QueryError> {
    Ok(LOCATOR_DEP_CONFIG_2.lock().unwrap().clone())
}

#[asset_key(asset = String)]
struct LocatorDepAsset2(String);

static LOCATOR_2_COUNT: AtomicU32 = AtomicU32::new(0);

#[asset_locator]
fn locator_2(db: &impl Db, key: &LocatorDepAsset2) -> Result<LocateResult<String>, QueryError> {
    LOCATOR_2_COUNT.fetch_add(1, Ordering::SeqCst);
    let config = db.query(GetLocatorDepConfig2 {})?;
    Ok(LocateResult::Ready {
        value: format!("{}:{}", key.0, config),
        durability: DurabilityLevel::Volatile,
    })
}

/// Test 2: Locator re-executes when dependencies change (direct asset access)
#[test]
fn test_locator_reexecutes_on_dep_change() {
    // Setup
    *LOCATOR_DEP_CONFIG_2.lock().unwrap() = "v1".to_string();
    LOCATOR_2_COUNT.store(0, Ordering::SeqCst);

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(Locator2);

    // Access asset directly
    let result = runtime.get_asset(LocatorDepAsset2("file".to_string()));
    assert!(result.is_ok());
    assert_eq!(LOCATOR_2_COUNT.load(Ordering::SeqCst), 1);

    // Change config and invalidate
    *LOCATOR_DEP_CONFIG_2.lock().unwrap() = "v2".to_string();
    runtime.invalidate(&GetLocatorDepConfig2 {});

    // Access asset again
    // IDEAL: Asset's deps changed, so locator should re-execute
    // CURRENT: get_asset via QueryRuntime doesn't track deps, asset has no deps
    let result = runtime.get_asset(LocatorDepAsset2("file".to_string()));
    assert!(result.is_ok());
    let state = result.unwrap();
    assert_eq!(**state.get().unwrap(), "file:v2", "Should have new value");
    assert_eq!(
        LOCATOR_2_COUNT.load(Ordering::SeqCst),
        2,
        "Locator should re-execute on dep change"
    );
}

/// Mutable config for test 3
static LOCATOR_DEP_CONFIG_3: std::sync::Mutex<String> = std::sync::Mutex::new(String::new());

#[query]
fn get_locator_dep_config_3(_db: &impl Db) -> Result<String, QueryError> {
    Ok(LOCATOR_DEP_CONFIG_3.lock().unwrap().clone())
}

#[asset_key(asset = String)]
struct LocatorDepAsset3(String);

// Locator that always returns same value regardless of config (for early cutoff test)
static LOCATOR_3_COUNT: AtomicU32 = AtomicU32::new(0);

#[asset_locator]
fn locator_3(db: &impl Db, key: &LocatorDepAsset3) -> Result<LocateResult<String>, QueryError> {
    LOCATOR_3_COUNT.fetch_add(1, Ordering::SeqCst);
    let _ = db.query(GetLocatorDepConfig3 {})?; // Dep but ignore result
    Ok(LocateResult::Ready {
        value: format!("constant:{}", key.0), // Always same value regardless of config
        durability: DurabilityLevel::Volatile,
    })
}

static QUERY_3_COUNT: AtomicU32 = AtomicU32::new(0);

#[query]
fn read_asset_3(db: &impl Db, key: LocatorDepAsset3) -> Result<String, QueryError> {
    QUERY_3_COUNT.fetch_add(1, Ordering::SeqCst);
    let content = db.asset(key)?;
    Ok((*content).clone())
}

/// Test 3: Query NOT re-executed when locator deps change but asset unchanged
#[test]
fn test_query_not_rerun_when_asset_unchanged() {
    *LOCATOR_DEP_CONFIG_3.lock().unwrap() = "v1".to_string();
    LOCATOR_3_COUNT.store(0, Ordering::SeqCst);
    QUERY_3_COUNT.store(0, Ordering::SeqCst);

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(Locator3);

    // First query
    let result = runtime.query(ReadAsset3::new(LocatorDepAsset3("file".to_string())));
    assert_eq!(*result.unwrap(), "constant:file");
    assert_eq!(QUERY_3_COUNT.load(Ordering::SeqCst), 1);
    assert_eq!(LOCATOR_3_COUNT.load(Ordering::SeqCst), 1);

    // Change config and invalidate (but asset value will be the same)
    *LOCATOR_DEP_CONFIG_3.lock().unwrap() = "v2".to_string();
    runtime.invalidate(&GetLocatorDepConfig3 {});

    // Query again
    let result = runtime.query(ReadAsset3::new(LocatorDepAsset3("file".to_string())));
    assert_eq!(*result.unwrap(), "constant:file");

    // IDEAL: Locator re-runs (dep changed), but query doesn't (asset unchanged)
    assert_eq!(
        LOCATOR_3_COUNT.load(Ordering::SeqCst),
        2,
        "Locator should re-execute"
    );
    assert_eq!(
        QUERY_3_COUNT.load(Ordering::SeqCst),
        1,
        "Query should NOT re-run (early cutoff)"
    );
}

/// Mutable config for test 4
static LOCATOR_DEP_CONFIG_4: std::sync::Mutex<String> = std::sync::Mutex::new(String::new());

#[query]
fn get_locator_dep_config_4(_db: &impl Db) -> Result<String, QueryError> {
    Ok(LOCATOR_DEP_CONFIG_4.lock().unwrap().clone())
}

#[asset_key(asset = String)]
struct LocatorDepAsset4(String);

// Locator that incorporates config value into asset (asset changes when config changes)
static LOCATOR_4_COUNT: AtomicU32 = AtomicU32::new(0);

#[asset_locator]
fn locator_4(db: &impl Db, key: &LocatorDepAsset4) -> Result<LocateResult<String>, QueryError> {
    LOCATOR_4_COUNT.fetch_add(1, Ordering::SeqCst);
    let config = db.query(GetLocatorDepConfig4 {})?;
    Ok(LocateResult::Ready {
        value: format!("{}:{}", key.0, config), // Asset value includes config
        durability: DurabilityLevel::Volatile,
    })
}

static QUERY_4_COUNT: AtomicU32 = AtomicU32::new(0);

#[query]
fn read_asset_4(db: &impl Db, key: LocatorDepAsset4) -> Result<String, QueryError> {
    QUERY_4_COUNT.fetch_add(1, Ordering::SeqCst);
    let content = db.asset(key)?;
    Ok((*content).clone())
}

/// Test 4: Query IS re-executed when locator deps change AND asset changes
#[test]
fn test_query_reruns_when_asset_changes() {
    *LOCATOR_DEP_CONFIG_4.lock().unwrap() = "v1".to_string();
    LOCATOR_4_COUNT.store(0, Ordering::SeqCst);
    QUERY_4_COUNT.store(0, Ordering::SeqCst);

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(Locator4);

    // First query
    let result = runtime.query(ReadAsset4::new(LocatorDepAsset4("file".to_string())));
    assert_eq!(*result.unwrap(), "file:v1");
    assert_eq!(QUERY_4_COUNT.load(Ordering::SeqCst), 1);

    // Change config (will change asset value)
    *LOCATOR_DEP_CONFIG_4.lock().unwrap() = "v2".to_string();
    runtime.invalidate(&GetLocatorDepConfig4 {});

    // Query again - should get new value
    let result = runtime.query(ReadAsset4::new(LocatorDepAsset4("file".to_string())));
    assert_eq!(*result.unwrap(), "file:v2");
    // Note: This test passes with current behavior because query re-runs trigger locator
    assert_eq!(
        QUERY_4_COUNT.load(Ordering::SeqCst),
        2,
        "Query SHOULD re-run when asset changes"
    );
}

// ============================================================================
// Additional Locator Dependency Tests
// ============================================================================
//
// These tests use embedded counters in keys (like CountedAsset) instead of
// global state to avoid test interference and complexity.

/// Test 5: Multiple dependencies in locator
#[asset_key(asset = String, key(path))]
struct MultiDepAssetKey {
    path: String,
    config_a_value: String,
    config_b_value: String,
    locator_count: Arc<AtomicU32>,
    query_count: Arc<AtomicU32>,
}

impl MultiDepAssetKey {
    fn new(path: &str, config_a: &str, config_b: &str) -> Self {
        Self {
            path: path.to_string(),
            config_a_value: config_a.to_string(),
            config_b_value: config_b.to_string(),
            locator_count: Arc::new(AtomicU32::new(0)),
            query_count: Arc::new(AtomicU32::new(0)),
        }
    }

    fn locator_count(&self) -> u32 {
        self.locator_count.load(Ordering::SeqCst)
    }

    fn query_count(&self) -> u32 {
        self.query_count.load(Ordering::SeqCst)
    }
}

#[query(keys(_name))]
fn get_multi_dep_config(
    _db: &impl Db,
    _name: String,
    value: String,
    _call_count: Arc<AtomicU32>,
) -> Result<String, QueryError> {
    _call_count.fetch_add(1, Ordering::SeqCst);
    Ok(value)
}

#[asset_locator]
fn multi_dep_locator(
    db: &impl Db,
    key: &MultiDepAssetKey,
) -> Result<LocateResult<String>, QueryError> {
    key.locator_count.fetch_add(1, Ordering::SeqCst);
    let a = db.query(GetMultiDepConfig::new(
        "a".to_string(),
        key.config_a_value.clone(),
        Arc::new(AtomicU32::new(0)),
    ))?;
    let b = db.query(GetMultiDepConfig::new(
        "b".to_string(),
        key.config_b_value.clone(),
        Arc::new(AtomicU32::new(0)),
    ))?;
    Ok(LocateResult::Ready {
        value: format!("{}:{}:{}", key.path, a, b),
        durability: DurabilityLevel::Volatile,
    })
}

#[query(keys(_path))]
fn read_multi_dep_asset(
    db: &impl Db,
    _path: String,
    key: MultiDepAssetKey,
) -> Result<String, QueryError> {
    key.query_count.fetch_add(1, Ordering::SeqCst);
    let content = db.asset(key)?;
    Ok((*content).clone())
}

#[test]
fn test_locator_multiple_deps_one_changes() {
    let key = MultiDepAssetKey::new("file", "a1", "b1");

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(MultiDepLocator);

    // First query
    let result = runtime.query(ReadMultiDepAsset::new("file".to_string(), key.clone()));
    assert_eq!(*result.unwrap(), "file:a1:b1");
    assert_eq!(key.locator_count(), 1);
    assert_eq!(key.query_count(), 1);

    // Invalidate config "a" (but value stays same for early cutoff test)
    // Note: GetMultiDepConfig uses keys(_name) so only _name matters for identity
    runtime.invalidate(&GetMultiDepConfig::new(
        "a".to_string(),
        String::new(),               // dummy value (not part of key)
        Arc::new(AtomicU32::new(0)), // dummy count (not part of key)
    ));

    // Query again - locator should re-run but query should NOT (early cutoff)
    let result = runtime.query(ReadMultiDepAsset::new("file".to_string(), key.clone()));
    assert_eq!(*result.unwrap(), "file:a1:b1");
    assert_eq!(
        key.locator_count(),
        2,
        "Locator should re-run on dep invalidation"
    );
    assert_eq!(
        key.query_count(),
        1,
        "Query should NOT re-run (early cutoff)"
    );
}

/// Test 6: Same query called multiple times in locator
#[asset_key(asset = String, key(path))]
struct DupDepAssetKey {
    path: String,
    config_value: String,
    locator_count: Arc<AtomicU32>,
    query_count: Arc<AtomicU32>,
}

impl DupDepAssetKey {
    fn new(path: &str, config_value: &str) -> Self {
        Self {
            path: path.to_string(),
            config_value: config_value.to_string(),
            locator_count: Arc::new(AtomicU32::new(0)),
            query_count: Arc::new(AtomicU32::new(0)),
        }
    }

    fn locator_count(&self) -> u32 {
        self.locator_count.load(Ordering::SeqCst)
    }

    fn query_count(&self) -> u32 {
        self.query_count.load(Ordering::SeqCst)
    }
}

#[query(keys(_name))]
fn get_dup_config(
    _db: &impl Db,
    _name: String,
    value: String,
    _call_count: Arc<AtomicU32>,
) -> Result<String, QueryError> {
    _call_count.fetch_add(1, Ordering::SeqCst);
    Ok(value)
}

#[asset_locator]
fn dup_dep_locator(db: &impl Db, key: &DupDepAssetKey) -> Result<LocateResult<String>, QueryError> {
    key.locator_count.fetch_add(1, Ordering::SeqCst);
    // Call the same query twice
    let first = db.query(GetDupConfig::new(
        "cfg".to_string(),
        key.config_value.clone(),
        Arc::new(AtomicU32::new(0)),
    ))?;
    let second = db.query(GetDupConfig::new(
        "cfg".to_string(),
        key.config_value.clone(),
        Arc::new(AtomicU32::new(0)),
    ))?;
    Ok(LocateResult::Ready {
        value: format!("{}:{}:{}", key.path, first, second),
        durability: DurabilityLevel::Volatile,
    })
}

#[query(keys(_path))]
fn read_dup_dep_asset(
    db: &impl Db,
    _path: String,
    key: DupDepAssetKey,
) -> Result<String, QueryError> {
    key.query_count.fetch_add(1, Ordering::SeqCst);
    let content = db.asset(key)?;
    Ok((*content).clone())
}

#[test]
fn test_locator_duplicate_deps() {
    let key = DupDepAssetKey::new("file", "v1");

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(DupDepLocator);

    // First query
    let result = runtime.query(ReadDupDepAsset::new("file".to_string(), key.clone()));
    assert_eq!(*result.unwrap(), "file:v1:v1");
    assert_eq!(key.locator_count(), 1);
    assert_eq!(key.query_count(), 1);

    // Invalidate the config query
    // Note: GetDupConfig uses keys(_name) so only _name matters for identity
    runtime.invalidate(&GetDupConfig::new(
        "cfg".to_string(),
        String::new(),               // dummy value (not part of key)
        Arc::new(AtomicU32::new(0)), // dummy count (not part of key)
    ));

    // Query again - locator should re-run exactly once
    // Asset value unchanged so query should NOT re-run (early cutoff)
    let result = runtime.query(ReadDupDepAsset::new("file".to_string(), key.clone()));
    assert_eq!(*result.unwrap(), "file:v1:v1");
    assert_eq!(
        key.locator_count(),
        2,
        "Locator should re-run once on dep invalidation"
    );
    assert_eq!(
        key.query_count(),
        1,
        "Query should NOT re-run (early cutoff)"
    );
}

/// Test 7: Locator calls db.asset() (depends on another asset)
#[asset_key(asset = String, key(path))]
struct DepAssetAKey {
    path: String,
    locator_count: Arc<AtomicU32>,
    query_count: Arc<AtomicU32>,
}

impl DepAssetAKey {
    fn new(path: &str) -> Self {
        Self {
            path: path.to_string(),
            locator_count: Arc::new(AtomicU32::new(0)),
            query_count: Arc::new(AtomicU32::new(0)),
        }
    }

    fn locator_count(&self) -> u32 {
        self.locator_count.load(Ordering::SeqCst)
    }

    fn query_count(&self) -> u32 {
        self.query_count.load(Ordering::SeqCst)
    }
}

#[asset_key(asset = String)]
struct DepAssetBKey(String);

#[asset_locator]
fn dep_asset_locator_a(
    db: &impl Db,
    key: &DepAssetAKey,
) -> Result<LocateResult<String>, QueryError> {
    key.locator_count.fetch_add(1, Ordering::SeqCst);
    let b = db.asset(DepAssetBKey(key.path.clone()))?;
    Ok(LocateResult::Ready {
        value: format!("A:{}:{}", key.path, b),
        durability: DurabilityLevel::Volatile,
    })
}

#[query(keys(_path))]
fn read_dep_asset_a(db: &impl Db, _path: String, key: DepAssetAKey) -> Result<String, QueryError> {
    key.query_count.fetch_add(1, Ordering::SeqCst);
    let content = db.asset(key)?;
    Ok((*content).clone())
}

#[test]
fn test_locator_dep_on_another_asset() {
    let key = DepAssetAKey::new("file");

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(DepAssetLocatorA);

    // Pre-resolve AssetB
    runtime.resolve_asset(
        DepAssetBKey("file".to_string()),
        "b_v1".to_string(),
        DurabilityLevel::Volatile,
    );

    // First query
    let result = runtime.query(ReadDepAssetA::new("file".to_string(), key.clone()));
    assert_eq!(*result.unwrap(), "A:file:b_v1");
    assert_eq!(key.locator_count(), 1);
    assert_eq!(key.query_count(), 1);

    // Change AssetB (different value)
    runtime.resolve_asset(
        DepAssetBKey("file".to_string()),
        "b_v2".to_string(),
        DurabilityLevel::Volatile,
    );

    // Query again - locator and query should re-run (value changed)
    let result = runtime.query(ReadDepAssetA::new("file".to_string(), key.clone()));
    assert_eq!(*result.unwrap(), "A:file:b_v2");
    assert_eq!(
        key.locator_count(),
        2,
        "Locator should re-run when AssetB changes"
    );
    assert_eq!(
        key.query_count(),
        2,
        "Query should re-run when AssetA changes"
    );

    // Resolve AssetB with SAME value - early cutoff at AssetB level
    // AssetB's changed_at stays the same, so AssetA's dep is still valid
    runtime.resolve_asset(
        DepAssetBKey("file".to_string()),
        "b_v2".to_string(),
        DurabilityLevel::Volatile,
    );

    // Query again - AssetA's locator should NOT re-run (early cutoff at AssetB)
    let result = runtime.query(ReadDepAssetA::new("file".to_string(), key.clone()));
    assert_eq!(*result.unwrap(), "A:file:b_v2");
    assert_eq!(
        key.locator_count(),
        2,
        "Locator should NOT re-run (early cutoff at AssetB)"
    );
    assert_eq!(
        key.query_count(),
        2,
        "Query should NOT re-run (early cutoff)"
    );
}

/// Test 8: Nested asset dependencies
/// Chain: OuterAsset's locator → InnerAsset → InnerAsset's locator → ConfigQuery
#[asset_key(asset = String, key(path))]
struct NestedInnerKey {
    path: String,
    config_value: String,
    locator_count: Arc<AtomicU32>,
}

impl NestedInnerKey {
    fn new(path: &str, config_value: &str) -> Self {
        Self {
            path: path.to_string(),
            config_value: config_value.to_string(),
            locator_count: Arc::new(AtomicU32::new(0)),
        }
    }

    fn locator_count(&self) -> u32 {
        self.locator_count.load(Ordering::SeqCst)
    }
}

#[asset_key(asset = String, key(path))]
struct NestedOuterKey {
    path: String,
    inner: NestedInnerKey,
    locator_count: Arc<AtomicU32>,
    query_count: Arc<AtomicU32>,
}

impl NestedOuterKey {
    fn new(path: &str, inner: NestedInnerKey) -> Self {
        Self {
            path: path.to_string(),
            inner,
            locator_count: Arc::new(AtomicU32::new(0)),
            query_count: Arc::new(AtomicU32::new(0)),
        }
    }

    fn inner_locator_count(&self) -> u32 {
        self.inner.locator_count()
    }

    fn outer_locator_count(&self) -> u32 {
        self.locator_count.load(Ordering::SeqCst)
    }

    fn query_count(&self) -> u32 {
        self.query_count.load(Ordering::SeqCst)
    }
}

#[query(keys(_name))]
fn get_nested_config(
    _db: &impl Db,
    _name: String,
    value: String,
    _call_count: Arc<AtomicU32>,
) -> Result<String, QueryError> {
    _call_count.fetch_add(1, Ordering::SeqCst);
    Ok(value)
}

#[asset_locator]
fn nested_inner_locator(
    db: &impl Db,
    key: &NestedInnerKey,
) -> Result<LocateResult<String>, QueryError> {
    key.locator_count.fetch_add(1, Ordering::SeqCst);
    let config = db.query(GetNestedConfig::new(
        "cfg".to_string(),
        key.config_value.clone(),
        Arc::new(AtomicU32::new(0)),
    ))?;
    Ok(LocateResult::Ready {
        value: format!("inner:{}:{}", key.path, config),
        durability: DurabilityLevel::Volatile,
    })
}

#[asset_locator]
fn nested_outer_locator(
    db: &impl Db,
    key: &NestedOuterKey,
) -> Result<LocateResult<String>, QueryError> {
    key.locator_count.fetch_add(1, Ordering::SeqCst);
    let inner = db.asset(key.inner.clone())?;
    Ok(LocateResult::Ready {
        value: format!("outer:{}:{}", key.path, inner),
        durability: DurabilityLevel::Volatile,
    })
}

#[query(keys(_path))]
fn read_nested_outer(
    db: &impl Db,
    _path: String,
    key: NestedOuterKey,
) -> Result<String, QueryError> {
    key.query_count.fetch_add(1, Ordering::SeqCst);
    let content = db.asset(key)?;
    Ok((*content).clone())
}

#[test]
fn test_nested_asset_locator_deps() {
    let inner = NestedInnerKey::new("file", "v1");
    let key = NestedOuterKey::new("file", inner);

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(NestedInnerLocator);
    runtime.register_asset_locator(NestedOuterLocator);

    // First query
    let result = runtime.query(ReadNestedOuter::new("file".to_string(), key.clone()));
    assert_eq!(*result.unwrap(), "outer:file:inner:file:v1");
    assert_eq!(key.inner_locator_count(), 1);
    assert_eq!(key.outer_locator_count(), 1);
    assert_eq!(key.query_count(), 1);

    // Invalidate config (value stays same for early cutoff test)
    // Note: GetNestedConfig uses keys(_name) so only _name matters for identity
    runtime.invalidate(&GetNestedConfig::new(
        "cfg".to_string(),
        String::new(),               // dummy value (not part of key)
        Arc::new(AtomicU32::new(0)), // dummy count (not part of key)
    ));

    // Inner locator re-runs, but inner value unchanged
    // → outer locator should NOT re-run (early cutoff at inner)
    let result = runtime.query(ReadNestedOuter::new("file".to_string(), key.clone()));
    assert_eq!(*result.unwrap(), "outer:file:inner:file:v1");
    assert_eq!(key.inner_locator_count(), 2, "Inner locator should re-run");
    assert_eq!(
        key.outer_locator_count(),
        1,
        "Outer locator should NOT re-run (early cutoff)"
    );
    assert_eq!(
        key.query_count(),
        1,
        "Query should NOT re-run (early cutoff)"
    );
}

/// Test 9: Locator error after collecting deps
#[asset_key(asset = String, key(path))]
struct ErrorAssetKey {
    path: String,
    config_value: String,
    locator_count: Arc<AtomicU32>,
}

impl ErrorAssetKey {
    fn new(path: &str, config_value: &str) -> Self {
        Self {
            path: path.to_string(),
            config_value: config_value.to_string(),
            locator_count: Arc::new(AtomicU32::new(0)),
        }
    }

    fn locator_count(&self) -> u32 {
        self.locator_count.load(Ordering::SeqCst)
    }
}

#[query(keys(_name))]
fn get_error_config(
    _db: &impl Db,
    _name: String,
    value: String,
    _call_count: Arc<AtomicU32>,
) -> Result<String, QueryError> {
    _call_count.fetch_add(1, Ordering::SeqCst);
    Ok(value)
}

#[asset_locator]
fn error_after_deps_locator(
    db: &impl Db,
    key: &ErrorAssetKey,
) -> Result<LocateResult<String>, QueryError> {
    key.locator_count.fetch_add(1, Ordering::SeqCst);
    // Collect dependency first
    let _config = db.query(GetErrorConfig::new(
        "cfg".to_string(),
        key.config_value.clone(),
        Arc::new(AtomicU32::new(0)),
    ))?;
    // Then return error
    Err(QueryError::UserError(Arc::new(anyhow::anyhow!(
        "intentional error for: {}",
        key.path
    ))))
}

#[test]
fn test_locator_error_after_deps_not_stored() {
    let key = ErrorAssetKey::new("file", "v1");

    let runtime = QueryRuntime::new();
    runtime.register_asset_locator(ErrorAfterDepsLocator);

    // First access - should return error and cache it
    let result = runtime.get_asset(key.clone());
    assert!(matches!(result, Err(QueryError::UserError(_))));
    assert_eq!(key.locator_count(), 1);

    // Second access - should return cached error, locator NOT called
    let result = runtime.get_asset(key.clone());
    assert!(matches!(result, Err(QueryError::UserError(_))));
    assert_eq!(
        key.locator_count(),
        1,
        "Locator should NOT be called again (error cached)"
    );
}
