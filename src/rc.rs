use std::sync::Arc;

#[cfg(not(feature = "concurrent-storage"))]
pub type CfgRc<T> = Rc<T>;
#[cfg(feature = "concurrent-storage")]
pub type CfgRc<T> = Arc<T>;
