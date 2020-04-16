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

//! Transaction pool prometheus metrics.

use prometheus_endpoint::{register, Counter, Gauge, PrometheusError, Registry, U64};

/// Transaction pool prometheus metrics.
pub struct Metrics {
	pub validation_pending: Gauge<U64>,
	pub total_validated: Counter<U64>,
}


impl Metrics {
	pub fn register(registry: &Registry) -> Result<Self, PrometheusError> {
		Ok(Self {
			validation_pending: register(
				Gauge::new(
					"sub_txpool_validation_pending",
					"Number of transactions scheduled for validation and not yet finished",
				)?,
				registry,
			)?,
			total_validated: register(
				Counter::new(
					"sub_txpool_total_validated",
					"Total number of validation requests performed",
				)?,
				registry,
			)?,
		})
	}
}
