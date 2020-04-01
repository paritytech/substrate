
use lazy_static::lazy_static;
use prometheus::{
    Registry, Error as PrometheusError, Opts,
    core::{
        GenericGaugeVec, AtomicU64,
        GenericGauge,
	}
};
use std::time::Instant;
use std::convert::TryFrom;
use parking_lot::Mutex;

use crate::channels::{ Sender, Receiver, OnFullStrategy, channel_with_strategy };

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

    pub static ref BLOCK_IMPORT: TimeSeriesCollector = TimeSeriesCollector::new();
}

lazy_static! {
    // Non public ones

	static ref BLOCK_IMPORT_INNER : GenericGaugeVec<AtomicU64> = GenericGaugeVec::new(
        Opts::new("block_import", "Block Import"),
        &["subtype"]
    ).expect("Creating of statics doesn't fail. qed");

}

struct TimeSeriesInfo {
	count: u64,
	lower_median: u64,
	median: u64,
	higher_median: u64,
	average: u64
}


impl From<Vec<u64>> for TimeSeriesInfo {
	fn from(mut input: Vec<u64>) -> Self {
		let count = input.len();
		if let Some(only_value) = match count {
			0 => Some(0),
			1 => Some(input[0]),
			_ => None
		} {
			return TimeSeriesInfo {
				count: u64::try_from(count).expect("Usize always fits into u64. qed"),
				lower_median: only_value,
				median: only_value,
				higher_median: only_value,
				average: only_value,
			}
		}

		input.sort();
		let median_pos = count.div_euclid(2);
		let median_dif = median_pos.div_euclid(2);
		let count = u64::try_from(count).expect("Usize always fits into u64. qed");
		let average = input.iter().fold(0u64, |acc, val| acc + val).div_euclid(count);

		TimeSeriesInfo {
			count,
			lower_median: input[median_pos - median_dif],
			median: input[median_pos],
			higher_median: input[median_pos + median_dif],
			average
		}
	}
}

/// Collecting aggregated timed series
pub struct TimeSeriesCollector {
    rx: Mutex<Receiver<u64>>,
    tx: Sender<u64>,
} 

pub struct Timer {
    tx: Sender<u64>,
    instant: Instant,
}

impl Drop for Timer {
    fn drop(&mut self) {
        if let Ok(mils) = u64::try_from(self.instant.elapsed().as_millis()) {
            self.tx.try_send(mils).expect("Doesn't fail on a Ring-buffered Channel. qed")
        }
    }
}

impl TimeSeriesCollector {
    pub fn new() -> Self {
        let (tx, rx) = channel_with_strategy(1000, OnFullStrategy::Ring);
        Self {
            rx: Mutex::new(rx), tx
        }
    }
    pub fn start_timer(&self) -> Timer {
        Timer {
            tx: self.tx.clone(),
            instant: Instant::now()
        }
    }
    fn aggregate(&self) -> TimeSeriesInfo {
        let mut entries = Vec::new();
        while let Ok((Some(val))) = self.rx.lock().try_next() {
            entries.push(val)
        }

        TimeSeriesInfo::from(entries)
    }
}

/// Register the statics to report to registry
pub fn register_globals(registry: &Registry) -> Result<(), PrometheusError> {
    registry.register(Box::new(TOKIO_THREADS_ALIVE.clone()))?;
    registry.register(Box::new(TOKIO_THREADS_TOTAL.clone()))?;
    registry.register(Box::new(UNBOUNDED_CHANNELS_COUNTER.clone()))?;
    registry.register(Box::new(BLOCK_IMPORT_INNER.clone()))?;
    Ok(())
}

/// Update the global meters to prometheus
pub fn tick() {

    let info = BLOCK_IMPORT.aggregate();
    BLOCK_IMPORT_INNER.with_label_values(&["count"]).set(info.count);
    BLOCK_IMPORT_INNER.with_label_values(&["time_average"]).set(info.average);
    BLOCK_IMPORT_INNER.with_label_values(&["time_median"]).set(info.median);
    BLOCK_IMPORT_INNER.with_label_values(&["time_lower_median"]).set(info.lower_median);
    BLOCK_IMPORT_INNER.with_label_values(&["time_higher_median"]).set(info.higher_median);

}