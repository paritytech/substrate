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
#[derive(Clone, Debug)]
pub struct Metrics {
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
	/// Number of sessions with lagging signed commitment on mandatory block
	pub beefy_lagging_sessions: Counter<U64>,
	/// Number of validator's trying to vote with no session initialized
	pub beefy_voting_with_no_session_initialized: Counter<U64>,
	/// Number of times no Authority public key found in store
	pub beefy_no_authority_found_in_store: Counter<U64>,
	/// Number of Buffered votes
	pub beefy_buffered_votes: Counter<U64>,
	/// Number of times Buffered votes is full
	pub beefy_buffered_votes_full: Counter<U64>,
	/// Number of Buffered justifications
	pub beefy_buffered_justifications: Counter<U64>,
	/// Number of times Buffered justifications is full
	pub beefy_buffered_justifications_full: Counter<U64>,
	/// Trying to set Best Beefy block to old block
	pub beefy_best_block_to_old_block: Gauge<U64>,
	/// Number of Successful handled votes
	pub beefy_successful_handled_votes: Counter<U64>,
	/// Number of Successful votes
	pub beefy_successful_votes: Counter<U64>,
	/// Number of Bad Justification imports
	pub beefy_bad_justification_imports: Gauge<U64>,
	/// Number of Good Justification imports
	pub beefy_good_justification_imports: Gauge<U64>,
	/// Number of Successful Justification respond request
	pub beefy_successful_justification_respond_request: Counter<U64>,
	/// Number of Failed Justification respond request
	pub beefy_failed_justification_respond_request: Counter<U64>,
	/// Number of On demand justification when there is no peer to request from
	pub beefy_on_demand_justification_no_peer_to_request_from: Counter<U64>,
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
			beefy_lagging_sessions: register(
				Counter::new(
					"substrate_beefy_lagging_sessions",
					"Number of sessions with lagging signed commitment on mandatory block",
				)?,
				registry,
			)?,
			beefy_voting_with_no_session_initialized: register(
				Counter::new(
					"substrate_voting_with_no_session_initialized",
					"Number of validator's trying to vote with no session initialized",
				)?,
				registry,
			)?,
			beefy_no_authority_found_in_store: register(
				Counter::new(
					"substrate_beefy_no_authority_found_in_store",
					"Number of times no Authority public key found in store",
				)?,
				registry,
			)?,
			beefy_buffered_votes: register(
				Counter::new("substrate_beefy_buffered_votes", "Number of Buffered votes")?,
				registry,
			)?,
			beefy_buffered_votes_full: register(
				Counter::new(
					"substrate_beefy_buffered_votes_full",
					"Number of times Buffered votes is full",
				)?,
				registry,
			)?,
			beefy_buffered_justifications: register(
				Counter::new(
					"substrate_beefy_buffered_justifications",
					"Number of Buffered justifications",
				)?,
				registry,
			)?,
			beefy_buffered_justifications_full: register(
				Counter::new(
					"substrate_beefy_buffered_justifications_full",
					"Number of times Buffered justifications is full",
				)?,
				registry,
			)?,
			beefy_best_block_to_old_block: register(
				Gauge::new(
					"substrate_beefy_best_block_to_old_block",
					"Trying to set Best Beefy block to old block",
				)?,
				registry,
			)?,
			beefy_successful_handled_votes: register(
				Counter::new(
					"substrate_beefy_successful_handled_votes",
					"Number of Successful handled votes",
				)?,
				registry,
			)?,
			beefy_successful_votes: register(
				Counter::new("substrate_beefy_successful_votes", "Number of Successful votes")?,
				registry,
			)?,
			beefy_bad_justification_imports: register(
				Gauge::new(
					"substrate_beefy_bad_justification_imports",
					"Number of Bad Justification imports",
				)?,
				registry,
			)?,
			beefy_good_justification_imports: register(
				Gauge::new(
					"substrate_beefy_good_justification_imports",
					"Number of Good Justification imports",
				)?,
				registry,
			)?,
			beefy_successful_justification_respond_request: register(
				Counter::new("substrate_beefy_successful_justification_respond_request", "Number of Successful Justification respond request")?,
				registry,
			)?,
			beefy_failed_justification_respond_request: register(
				Counter::new("substrate_beefy_failed_justification_respond_request", "Number of Failed Justification respond request")?,
				registry,
			)?,
			beefy_on_demand_justification_no_peer_to_request_from: register(
				Counter::new("substrate_beefy_on_demand_justification_no_peer_to_request_from", "Number of on demand justification when there is no peer to request from")?,
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
