// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! [Grafana] data source server
//!
//! To display node statistics with [Grafana], this module exposes a `run_server` function that
//! starts up a HTTP server that conforms to the [`grafana-json-data-source`] API. The
//! `record_metrics` macro can be used to pass metrics to this server.
//!
//! [Grafana]: https://grafana.com/
//! [`grafana-json-data-source`]: https://github.com/simPod/grafana-json-datasource

use lazy_static::lazy_static;
use std::collections::HashMap;
use parking_lot::RwLock;

mod types;
mod server;
mod util;
#[cfg(not(target_os = "unknown"))]
mod networking;

pub use server::run_server;
pub use util::now_millis;

type Metrics = HashMap<String, Vec<(f32, i64)>>;

lazy_static! {
	/// The `RwLock` wrapping the metrics. Not intended to be used directly.
	#[doc(hidden)]
	pub static ref METRICS: RwLock<Metrics> = RwLock::new(Metrics::new());
}

/// Write metrics to `METRICS`.
#[macro_export]
macro_rules! record_metrics(
	($($key:expr => $value:expr),*) => {
		use $crate::{METRICS, now_millis};
		let mut metrics = METRICS.write();
		let now = now_millis();
		$(
			metrics.entry($key).or_insert_with(Vec::new).push(($value as f32, now));
		)*
	}
);
