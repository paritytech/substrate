
use lazy_static::lazy_static;
use prometheus::{
    Registry, Error as PrometheusError, Opts,
    Histogram, HistogramOpts, 
    core::{
        GenericGaugeVec, AtomicU64,
        GenericGauge,
	}
};

lazy_static! {

    pub static ref TOKIO_THREADS_TOTAL: GenericGauge<AtomicU64> = GenericGauge::new(
        "tokio_threads_total", "Total number of threads created"
    ).expect("Creating of statics doesn't fail. qed");

    pub static ref TOKIO_THREADS_ALIVE: GenericGauge<AtomicU64> = GenericGauge::new(
        "tokio_threads_alive", "Number of threads alive right now"
    ).expect("Creating of statics doesn't fail. qed");

	pub static ref UNBOUNDED_CHANNELS_COUNTER : GenericGaugeVec<AtomicU64> = GenericGaugeVec::new(
        Opts::new("internals_unbounded_channels", "items in each mpsc::unbounded instance"),
        &["entity"]
    ).expect("Creating of statics doesn't fail. qed");

	pub static ref BLOCK_IMPORT : Histogram = Histogram::with_opts(
        HistogramOpts::new("block_import", "Block Import"),
    ).expect("Creating of statics doesn't fail. qed");
}

/// Register the statics to report to registry
pub fn register_globals(registry: &Registry) -> Result<(), PrometheusError> {
    registry.register(Box::new(TOKIO_THREADS_ALIVE.clone()))?;
    registry.register(Box::new(TOKIO_THREADS_TOTAL.clone()))?;
    registry.register(Box::new(UNBOUNDED_CHANNELS_COUNTER.clone()))?;
    Ok(())
}