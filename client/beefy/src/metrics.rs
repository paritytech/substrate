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

//! BEEFY Prometheus metrics definition

use prometheus::{register, Counter, Gauge, PrometheusError, Registry, U64};

/// BEEFY metrics exposed through Prometheus
pub(crate) struct Metrics {
	/// Current active validator set id
	pub beefy_validator_set_id: Gauge<U64>,
	pub beefy_gadget_votes: Counter<U64>,
}

impl Metrics {
	pub(crate) fn register(registry: &Registry) -> Result<Self, PrometheusError> {
		Ok(Self {
			beefy_validator_set_id: register(
				Gauge::new("beefy_validator_set_id", "Current BEEFY active validator set id.")?,
				registry,
			)?,
			beefy_gadget_votes: register(
				Counter::new("beefy_gadget_votes_total", "Total number of vote messages gossiped.")?,
				registry,
			)?,
		})
	}
}
