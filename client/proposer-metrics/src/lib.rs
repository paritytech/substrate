// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Prometheus basic proposer metrics.

use prometheus_endpoint::{register, PrometheusError, Registry, Histogram, HistogramOpts, Gauge, U64};

/// Optional shareable link to basic authorship metrics.
#[derive(Clone, Default)]
pub struct MetricsLink(Option<Metrics>);

impl MetricsLink {
	pub fn new(registry: Option<&Registry>) -> Self {
		Self(
			registry.and_then(|registry|
				Metrics::register(registry)
					.map_err(|err| log::warn!("Failed to register proposer prometheus metrics: {}", err))
					.ok()
			)
		)
	}

	pub fn report<O>(&self, do_this: impl FnOnce(&Metrics) -> O) -> Option<O> {
		Some(do_this(self.0.as_ref()?))
	}
}

/// Authorship metrics.
#[derive(Clone)]
pub struct Metrics {
	pub block_constructed: Histogram,
	pub number_of_transactions: Gauge<U64>,
}

impl Metrics {
	pub fn register(registry: &Registry) -> Result<Self, PrometheusError> {
		Ok(Self {
			block_constructed: register(
				Histogram::with_opts(HistogramOpts::new(
					"proposer_block_constructed",
					"Histogram of time taken to construct new block",
				))?,
				registry,
			)?,
			number_of_transactions: register(
				Gauge::new(
					"proposer_number_of_transactions",
					"Number of transactions included in block",
				)?,
				registry,
			)?,
		})
	}
}
