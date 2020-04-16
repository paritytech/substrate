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

use prometheus_endpoint::{register, Counter, PrometheusError, Registry, U64};

/// Transaction pool Prometheus metrics.
pub struct Metrics {
	pub validations_scheduled: Counter<U64>,
	pub validations_finished: Counter<U64>,
}


impl Metrics {
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
