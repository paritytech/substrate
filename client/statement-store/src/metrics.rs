// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Statement store Prometheus metrics.

use std::sync::Arc;

use prometheus_endpoint::{register, Counter, PrometheusError, Registry, U64};

#[derive(Clone, Default)]
pub struct MetricsLink(Arc<Option<Metrics>>);

impl MetricsLink {
	pub fn new(registry: Option<&Registry>) -> Self {
		Self(Arc::new(registry.and_then(|registry| {
			Metrics::register(registry)
				.map_err(|err| {
					log::warn!("Failed to register prometheus metrics: {}", err);
				})
				.ok()
		})))
	}

	pub fn report(&self, do_this: impl FnOnce(&Metrics)) {
		if let Some(metrics) = self.0.as_ref() {
			do_this(metrics);
		}
	}
}

/// Statement store Prometheus metrics.
pub struct Metrics {
	pub submitted_statements: Counter<U64>,
	pub validations_invalid: Counter<U64>,
	pub statements_pruned: Counter<U64>,
}

impl Metrics {
	pub fn register(registry: &Registry) -> Result<Self, PrometheusError> {
		Ok(Self {
			submitted_statements: register(
				Counter::new(
					"substrate_sub_statement_store_submitted_statements",
					"Total number of statements submitted",
				)?,
				registry,
			)?,
			validations_invalid: register(
				Counter::new(
					"substrate_sub_statement_store_validations_invalid",
					"Total number of statements that were removed from the pool as invalid",
				)?,
				registry,
			)?,
			statements_pruned: register(
				Counter::new(
					"substrate_sub_statement_store_block_statements",
					"Total number of statements that was requested to be pruned by block events",
				)?,
				registry,
			)?,
		})
	}
}
