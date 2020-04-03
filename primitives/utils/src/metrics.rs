
use lazy_static::lazy_static;
use prometheus::{
    Registry, Error as PrometheusError, Opts,
    core::{
        GenericGaugeVec, AtomicU64,
        GenericGauge, GenericCounter
	}
};

lazy_static! {

    pub static ref TOKIO_THREADS_TOTAL: GenericCounter<AtomicU64> = GenericCounter::new(
        "tokio_threads_total", "Total number of threads created"
    ).expect("Creating of statics doesn't fail. qed");

    pub static ref TOKIO_THREADS_ALIVE: GenericGauge<AtomicU64> = GenericGauge::new(
        "tokio_threads_alive", "Number of threads alive right now"
    ).expect("Creating of statics doesn't fail. qed");

	pub static ref UNBOUNDED_CHANNELS_COUNTER : GenericGaugeVec<AtomicU64> = GenericGaugeVec::new(
        Opts::new("unbounded_channel_len", "Items in each mpsc::unbounded instance"),
        &["entity","action"] // 'name of channel, send|received|dropped
    ).expect("Creating of statics doesn't fail. qed");

}


/// Register the statics to report to registry
pub fn register_globals(registry: &Registry) -> Result<(), PrometheusError> {
    registry.register(Box::new(TOKIO_THREADS_ALIVE.clone()))?;
    registry.register(Box::new(TOKIO_THREADS_TOTAL.clone()))?;
    registry.register(Box::new(UNBOUNDED_CHANNELS_COUNTER.clone()))?;
    Ok(())
}
