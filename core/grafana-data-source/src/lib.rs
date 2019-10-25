use lazy_static::lazy_static;
use chrono::DateTime;
use std::collections::HashMap;
use parking_lot::RwLock;

mod types;
mod server;
pub use server::run_server;
pub use chrono::Utc;

type Metrics = HashMap<&'static str, Vec<(f32, DateTime<Utc>)>>;

lazy_static! {
    pub static ref METRICS: RwLock<Metrics> = RwLock::new(Metrics::new());
}

#[macro_export]
macro_rules! record_metrics(
	($($key:expr => $value:expr),*) => {
		use $crate::{Utc, METRICS};
		let mut metrics = METRICS.write();
		let now = Utc::now();
		$(
			metrics.entry($key).or_insert_with(Vec::new).push(($value as f32, now));
		)*
	}
);