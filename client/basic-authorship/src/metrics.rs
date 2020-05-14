// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! Transaction pool Prometheus metrics.

use std::sync::Arc;

use prometheus_endpoint::{register, PrometheusError, Registry, Histogram, HistogramOpts};
#[derive(Clone, Default)]
pub struct MetricsLink(Arc<Option<Metrics>>);

impl MetricsLink {
	pub fn new(registry: Option<&Registry>) -> Self {
		Self(Arc::new(
			registry.and_then(|registry|
				Metrics::register(registry)
					.map_err(|err| { log::warn!("Failed to register prometheus metrics: {}", err); })
					.ok()
			)
		))
	}

	pub fn report(&self, do_this: impl FnOnce(&Metrics)) {
		if let Some(metrics) = self.0.as_ref() {
			do_this(metrics);
		}
	}
}
/// Authorship metrics.
pub struct Metrics {
	pub block_constructed: Histogram,
}

impl Metrics {
	pub fn register(registry: &Registry) -> Result<Self, PrometheusError> {
		Ok(Self {
			block_constructed: register(
				Histogram::with_opts(HistogramOpts::new(
					"sub_proposer_block_constructed",
					"Histogram of time taken to construct new block",
				))?,
				registry,
			)?,
		})
	}
}
