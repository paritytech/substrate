
use lazy_static::lazy_static;
use parking_lot::RwLock;
use std::collections::HashMap;

lazy_static! {
    pub static ref GLOBAL_METRICS: InternalMetrics = InternalMetrics::new();
}

pub struct InternalMetrics {
    metrics: RwLock<HashMap<&'static str, u64>>,
    series: RwLock<Vec<(&'static str, u64)>>
}

impl InternalMetrics {
    pub fn new() -> Self {
        Self {
            metrics: RwLock::new(HashMap::new()),
            series: RwLock::new(Vec::new())
        }
    }

    pub fn incr(&self, key: &'static str) {
        self.incr_by(key, 1)
    }

    pub fn incr_by(&self, key: &'static str, value: u64) {
        let mut h = self.metrics.write();
        h.entry(key)
            .and_modify(|v| {
                *v = v.checked_add(value).unwrap_or(u64::MAX)
            })
            .or_insert(value);
    }

    pub fn decr(&self, key: &'static str) {
        self.decr_by(key, 1);
    }

    pub fn decr_by(&self, key: &'static str, value: u64) {
        let mut h = self.metrics.write();
        h.entry(key)
            .and_modify(|v| {
                *v = v.checked_sub(value).unwrap_or(0)
            })
            .or_insert(0);
    }

    pub fn set(&self, key: &'static str, value: u64) {
        self.metrics.write().insert(key, value);
    }

    pub fn add(&self, key: &'static str, value: u64) {
        self.series.write().push((key, value))
    }

    pub fn get(&self, key: &'static str) -> Option<u64> {
        self.metrics.read().get(key).cloned()
    }

    pub fn inner<'a>(&'a self) -> &'a RwLock<HashMap<&'static str, u64>> {
        &self.metrics
    }

    pub fn flush_series(&self) -> Vec<(&'static str, u64)> {
        self.series.write().drain(..).collect::<Vec<_>>()
    }
}