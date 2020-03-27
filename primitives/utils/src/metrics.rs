
use lazy_static::lazy_static;
use parking_lot::RwLock;
use std::collections::HashMap;

lazy_static! {
    /// Globally available metrics collector
    pub static ref GLOBAL_METRICS: InternalMetrics = InternalMetrics::new();
}

/// Simple globally availble cache for internal measures, trackingthe count of any
/// `'static str` as an `u64`. Alternatively collect sets of counts
/// (that are typically averaged).
pub struct InternalMetrics {
    metrics: RwLock<HashMap<&'static str, u64>>,
    series: RwLock<Vec<(&'static str, u64)>>
}

impl InternalMetrics {
    /// Create a new instance
    fn new() -> Self {
        Self {
            metrics: RwLock::new(HashMap::new()),
            series: RwLock::new(Vec::new())
        }
    }

    /// Increment the counter at `key`
    pub fn incr(&self, key: &'static str) {
        self.incr_by(key, 1)
    }

    /// Increment the counter at `key` by `value`
    pub fn incr_by(&self, key: &'static str, value: u64) {
        let mut h = self.metrics.write();
        h.entry(key)
            .and_modify(|v| {
                *v = v.checked_add(value).unwrap_or(u64::MAX)
            })
            .or_insert(value);
    }

    /// Decrement the counter at `key`
    pub fn decr(&self, key: &'static str) {
        self.decr_by(key, 1);
    }

    /// Deccrement the counter at `key` by `value`
    pub fn decr_by(&self, key: &'static str, value: u64) {
        let mut h = self.metrics.write();
        h.entry(key)
            .and_modify(|v| {
                *v = v.checked_sub(value).unwrap_or(0)
            })
            .or_insert(0);
    }

    /// Set the counter at `key` to `value`
    pub fn set(&self, key: &'static str, value: u64) {
        self.metrics.write().insert(key, value);
    }

    /// Add then `value` to the series at `key`
    pub fn add(&self, key: &'static str, value: u64) {
        self.series.write().push((key, value))
    }

    /// Get the current `value` of `key`
    pub fn get(&self, key: &'static str) -> Option<u64> {
        self.metrics.read().get(key).cloned()
    }

    /// Get the inner HashMap of counters
    pub fn inner<'a>(&'a self) -> &'a RwLock<HashMap<&'static str, u64>> {
        &self.metrics
    }

    /// Flush the series and return them
    pub fn flush_series(&self) -> Vec<(&'static str, u64)> {
        self.series.write().drain(..).collect::<Vec<_>>()
    }
}