// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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
	/// Total number of votes sent by this node
	pub beefy_votes_sent: Counter<U64>,
	/// Most recent concluded voting round
	pub beefy_round_concluded: Gauge<U64>,
	/// Best block finalized by BEEFY
	pub beefy_best_block: Gauge<U64>,
	/// Next block BEEFY should vote on
	pub beefy_should_vote_on: Gauge<U64>,
	/// Number of sessions without a signed commitment
	pub beefy_skipped_sessions: Counter<U64>,
}

impl Metrics {
	pub(crate) fn register(registry: &Registry) -> Result<Self, PrometheusError> {
		Ok(Self {
			beefy_validator_set_id: register(
				Gauge::new(
					"substrate_beefy_validator_set_id",
					"Current BEEFY active validator set id.",
				)?,
				registry,
			)?,
			beefy_votes_sent: register(
				Counter::new("substrate_beefy_votes_sent", "Number of votes sent by this node")?,
				registry,
			)?,
			beefy_round_concluded: register(
				Gauge::new(
					"substrate_beefy_round_concluded",
					"Voting round, that has been concluded",
				)?,
				registry,
			)?,
			beefy_best_block: register(
				Gauge::new("substrate_beefy_best_block", "Best block finalized by BEEFY")?,
				registry,
			)?,
			beefy_should_vote_on: register(
				Gauge::new("substrate_beefy_should_vote_on", "Next block, BEEFY should vote on")?,
				registry,
			)?,
			beefy_skipped_sessions: register(
				Counter::new(
					"substrate_beefy_skipped_sessions",
					"Number of sessions without a signed commitment",
				)?,
				registry,
			)?,
		})
	}
}

// Note: we use the `format` macro to convert an expr into a `u64`. This will fail,
// if expr does not derive `Display`.
#[macro_export]
macro_rules! metric_set {
	($self:ident, $m:ident, $v:expr) => {{
		let val: u64 = format!("{}", $v).parse().unwrap();

		if let Some(metrics) = $self.metrics.as_ref() {
			metrics.$m.set(val);
		}
	}};
}

#[macro_export]
macro_rules! metric_inc {
	($self:ident, $m:ident) => {{
		if let Some(metrics) = $self.metrics.as_ref() {
			metrics.$m.inc();
		}
	}};
}

#[cfg(test)]
#[macro_export]
macro_rules! metric_get {
	($self:ident, $m:ident) => {{
		$self.metrics.as_ref().map(|metrics| metrics.$m.clone())
	}};
}
