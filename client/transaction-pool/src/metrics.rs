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

//! Transaction pool Prometheus metrics.

use std::sync::Arc;

use prometheus_endpoint::{register, Counter, PrometheusError, Registry, U64};

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

/// Transaction pool Prometheus metrics.
pub struct Metrics {
	pub submitted_transactions: Counter<U64>,
	pub validations_invalid: Counter<U64>,
	pub block_transactions_pruned: Counter<U64>,
	pub block_transactions_resubmitted: Counter<U64>,
}

impl Metrics {
	pub fn register(registry: &Registry) -> Result<Self, PrometheusError> {
		Ok(Self {
			submitted_transactions: register(
				Counter::new(
					"sub_txpool_submitted_transactions",
					"Total number of transactions submitted",
				)?,
				registry,
			)?,
			validations_invalid: register(
				Counter::new(
					"sub_txpool_validations_invalid",
					"Total number of transactions that were removed from the pool as invalid",
				)?,
				registry,
			)?,
			block_transactions_pruned: register(
				Counter::new(
					"sub_txpool_block_transactions_pruned",
					"Total number of transactions that was requested to be pruned by block events",
				)?,
				registry,
			)?,
			block_transactions_resubmitted: register(
				Counter::new(
					"sub_txpool_block_transactions_resubmitted",
					"Total number of transactions that was requested to be resubmitted by block events",
				)?,
				registry,
			)?,
		})
	}
}

/// Transaction pool api Prometheus metrics.
pub struct ApiMetrics {
	pub validations_scheduled: Counter<U64>,
	pub validations_finished: Counter<U64>,
}

impl ApiMetrics {
	/// Register the metrics at the given Prometheus registry.
	pub fn register(registry: &Registry) -> Result<Self, PrometheusError> {
		Ok(Self {
			validations_scheduled: register(
				Counter::new(
					"sub_txpool_validations_scheduled",
					"Total number of transactions scheduled for validation",
				)?,
				registry,
			)?,
			validations_finished: register(
				Counter::new(
					"sub_txpool_validations_finished",
					"Total number of transactions that finished validation",
				)?,
				registry,
			)?,
		})
	}
}

/// An extension trait for [`ApiMetrics`].
pub trait ApiMetricsExt {
	/// Report an event to the metrics.
	fn report(&self, report: impl FnOnce(&ApiMetrics));
}

impl ApiMetricsExt for Option<Arc<ApiMetrics>> {
	fn report(&self, report: impl FnOnce(&ApiMetrics)) {
		if let Some(metrics) = self.as_ref() {
			report(metrics)
		}
	}
}
