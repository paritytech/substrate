// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

#![warn(missing_docs)]

use lazy_static::lazy_static;
use parking_lot::RwLock;

mod types;
mod server;
#[cfg(not(target_os = "unknown"))]
mod networking;
mod database;

use database::Database;
pub use server::run_server;
use std::num::TryFromIntError;

lazy_static! {
	// The `RwLock` wrapping the metrics database.
	static ref DATABASE: RwLock<Database> = RwLock::new(Database::new());
}

/// Write metrics to `METRICS`.
#[macro_export]
macro_rules! record_metrics(
	($($key:expr => $value:expr,)*) => {
		if cfg!(not(target_os = "unknown")) {
			$crate::record_metrics_slice(&[
				$( ($key, $value as f32), )*
			])
		} else {
			Ok(())
		}
	}
);

/// Write metrics to `METRICS` as a slice. Intended to be only used via `record_metrics!`.
pub fn record_metrics_slice(metrics: &[(&str, f32)]) -> Result<(), Error> {
	let mut database = crate::DATABASE.write();

	for &(key, value) in metrics.iter() {
		database.push(key, value)?;
	}

	Ok(())
}

/// Error type that can be returned by either `record_metrics` or `run_server`.
#[derive(Debug, derive_more::Display, derive_more::From)]
pub enum Error {
	/// Hyper internal error.
	#[cfg(not(target_os = "unknown"))]
	Hyper(hyper::Error),
	/// Http request error.
	#[cfg(not(target_os = "unknown"))]
	Http(hyper::http::Error),
	/// Serialization/deserialization error.
	Serde(serde_json::Error),
	/// Timestamp error.
	Timestamp(TryFromIntError),
	/// i/o error.
	Io(std::io::Error)
}

impl std::error::Error for Error {
	fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
		match self {
			#[cfg(not(target_os = "unknown"))]
			Error::Hyper(error) => Some(error),
			#[cfg(not(target_os = "unknown"))]
			Error::Http(error) => Some(error),
			Error::Serde(error) => Some(error),
			Error::Timestamp(error) => Some(error),
			Error::Io(error) => Some(error)
		}
	}
}
