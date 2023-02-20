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

use log::debug;
use prometheus::{register, Counter, Gauge, PrometheusError, Registry, U64};

/// Helper trait for registering BEEFY metrics to Prometheus registry.
pub(crate) trait PrometheusRegister<T: Sized = Self>: Sized {
	const DESCRIPTION: &'static str;
	fn register(registry: &Registry) -> Result<Self, PrometheusError>;
}

/// BEEFY voting-related metrics exposed through Prometheus
#[derive(Clone, Debug)]
pub struct VoterMetrics {
	/// Current active validator set id
	pub beefy_validator_set_id: Gauge<U64>,
	/// Total number of votes sent by this node
	pub beefy_votes_sent: Counter<U64>,
	/// Best block finalized by BEEFY
	pub beefy_best_block: Gauge<U64>,
	/// Best block BEEFY voted on
	pub beefy_best_voted: Gauge<U64>,
	/// Next block BEEFY should vote on
	pub beefy_should_vote_on: Gauge<U64>,
	/// Number of sessions with lagging signed commitment on mandatory block
	pub beefy_lagging_sessions: Counter<U64>,
	/// Number of times no Authority public key found in store
	pub beefy_no_authority_found_in_store: Counter<U64>,
	/// Number of currently buffered votes
	pub beefy_buffered_votes: Gauge<U64>,
	/// Number of votes dropped due to full buffers
	pub beefy_buffered_votes_dropped: Counter<U64>,
	/// Number of good votes successfully handled
	pub beefy_good_votes_processed: Counter<U64>,
	/// Number of equivocation votes received
	pub beefy_equivocation_votes: Counter<U64>,
	/// Number of invalid votes received
	pub beefy_invalid_votes: Counter<U64>,
	/// Number of valid but stale votes received
	pub beefy_stale_votes: Counter<U64>,
	/// Number of currently buffered justifications
	pub beefy_buffered_justifications: Gauge<U64>,
	/// Number of valid but stale justifications received
	pub beefy_stale_justifications: Counter<U64>,
	/// Number of valid justifications successfully imported
	pub beefy_imported_justifications: Counter<U64>,
	/// Number of justifications dropped due to full buffers
	pub beefy_buffered_justifications_dropped: Counter<U64>,
	/// Trying to set Best Beefy block to old block
	pub beefy_best_block_set_last_failure: Gauge<U64>,
}

impl PrometheusRegister for VoterMetrics {
	const DESCRIPTION: &'static str = "voter";
	fn register(registry: &Registry) -> Result<Self, PrometheusError> {
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
			beefy_best_block: register(
				Gauge::new("substrate_beefy_best_block", "Best block finalized by BEEFY")?,
				registry,
			)?,
			beefy_best_voted: register(
				Gauge::new("substrate_beefy_best_voted", "Best block voted on by BEEFY")?,
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
			beefy_no_authority_found_in_store: register(
				Counter::new(
					"substrate_beefy_no_authority_found_in_store",
					"Number of times no Authority public key found in store",
				)?,
				registry,
			)?,
			beefy_buffered_votes: register(
				Gauge::new("substrate_beefy_buffered_votes", "Number of currently buffered votes")?,
				registry,
			)?,
			beefy_buffered_votes_dropped: register(
				Counter::new(
					"substrate_beefy_buffered_votes_dropped",
					"Number of votes dropped due to full buffers",
				)?,
				registry,
			)?,
			beefy_good_votes_processed: register(
				Counter::new(
					"substrate_beefy_successful_handled_votes",
					"Number of good votes successfully handled",
				)?,
				registry,
			)?,
			beefy_equivocation_votes: register(
				Counter::new(
					"substrate_beefy_stale_votes",
					"Number of equivocation votes received",
				)?,
				registry,
			)?,
			beefy_invalid_votes: register(
				Counter::new("substrate_beefy_stale_votes", "Number of invalid votes received")?,
				registry,
			)?,
			beefy_stale_votes: register(
				Counter::new(
					"substrate_beefy_stale_votes",
					"Number of valid but stale votes received",
				)?,
				registry,
			)?,
			beefy_buffered_justifications: register(
				Gauge::new(
					"substrate_beefy_buffered_justifications",
					"Number of currently buffered justifications",
				)?,
				registry,
			)?,
			beefy_stale_justifications: register(
				Counter::new(
					"substrate_beefy_stale_justifications",
					"Number of valid but stale justifications received",
				)?,
				registry,
			)?,
			beefy_imported_justifications: register(
				Counter::new(
					"substrate_beefy_imported_justifications",
					"Number of valid justifications successfully imported",
				)?,
				registry,
			)?,
			beefy_buffered_justifications_dropped: register(
				Counter::new(
					"substrate_beefy_buffered_justifications_dropped",
					"Number of justifications dropped due to full buffers",
				)?,
				registry,
			)?,
			beefy_best_block_set_last_failure: register(
				Gauge::new(
					"substrate_beefy_best_block_to_old_block",
					"Trying to set Best Beefy block to old block",
				)?,
				registry,
			)?,
		})
	}
}

/// BEEFY block-import-related metrics exposed through Prometheus
#[derive(Clone, Debug)]
pub struct BlockImportMetrics {
	/// Number of Good Justification imports
	pub beefy_good_justification_imports: Counter<U64>,
	/// Number of Bad Justification imports
	pub beefy_bad_justification_imports: Counter<U64>,
}

impl PrometheusRegister for BlockImportMetrics {
	const DESCRIPTION: &'static str = "block-import";
	fn register(registry: &Registry) -> Result<Self, PrometheusError> {
		Ok(Self {
			beefy_good_justification_imports: register(
				Counter::new(
					"substrate_beefy_good_justification_imports",
					"Number of Good Justification imports",
				)?,
				registry,
			)?,
			beefy_bad_justification_imports: register(
				Counter::new(
					"substrate_beefy_bad_justification_imports",
					"Number of Bad Justification imports",
				)?,
				registry,
			)?,
		})
	}
}

/// BEEFY on-demand-justifications-related metrics exposed through Prometheus
#[derive(Clone, Debug)]
pub struct OnDemandIncomingRequestsMetrics {
	/// Number of Successful Justification responses
	pub beefy_successful_justification_responses: Counter<U64>,
	/// Number of Failed Justification responses
	pub beefy_failed_justification_responses: Counter<U64>,
}

impl PrometheusRegister for OnDemandIncomingRequestsMetrics {
	const DESCRIPTION: &'static str = "on-demand incoming justification requests";
	fn register(registry: &Registry) -> Result<Self, PrometheusError> {
		Ok(Self {
			beefy_successful_justification_responses: register(
				Counter::new(
					"substrate_beefy_successful_justification_responses",
					"Number of Successful Justification responses",
				)?,
				registry,
			)?,
			beefy_failed_justification_responses: register(
				Counter::new(
					"substrate_beefy_failed_justification_responses",
					"Number of Failed Justification responses",
				)?,
				registry,
			)?,
		})
	}
}

/// BEEFY on-demand-justifications-related metrics exposed through Prometheus
#[derive(Clone, Debug)]
pub struct OnDemandOutgoingRequestsMetrics {
	/// Number of times there was no good peer to request justification from
	pub beefy_on_demand_justification_no_peer_to_request_from: Counter<U64>,
	/// Number of on-demand justification peer hang up
	pub beefy_on_demand_justification_peer_hang_up: Counter<U64>,
	/// Number of on-demand justification peer error
	pub beefy_on_demand_justification_peer_error: Counter<U64>,
	/// Number of on-demand justification invalid proof
	pub beefy_on_demand_justification_invalid_proof: Counter<U64>,
	/// Number of on-demand justification good proof
	pub beefy_on_demand_justification_good_proof: Counter<U64>,
}

impl PrometheusRegister for OnDemandOutgoingRequestsMetrics {
	const DESCRIPTION: &'static str = "on-demand outgoing justification requests";
	fn register(registry: &Registry) -> Result<Self, PrometheusError> {
		Ok(Self {
			beefy_on_demand_justification_no_peer_to_request_from: register(
				Counter::new(
					"substrate_beefy_on_demand_justification_no_peer_to_request_from",
					"Number of times there was no good peer to request justification from",
				)?,
				registry,
			)?,
			beefy_on_demand_justification_peer_hang_up: register(
				Counter::new(
					"substrate_beefy_on_demand_justification_peer_hang_up",
					"Number of on-demand justification peer hang up",
				)?,
				registry,
			)?,
			beefy_on_demand_justification_peer_error: register(
				Counter::new(
					"substrate_beefy_on_demand_justification_peer_error",
					"Number of on-demand justification peer error",
				)?,
				registry,
			)?,
			beefy_on_demand_justification_invalid_proof: register(
				Counter::new(
					"substrate_beefy_on_demand_justification_invalid_proof",
					"Number of on-demand justification invalid proof",
				)?,
				registry,
			)?,
			beefy_on_demand_justification_good_proof: register(
				Counter::new(
					"substrate_beefy_on_demand_justification_good_proof",
					"Number of on-demand justification good proof",
				)?,
				registry,
			)?,
		})
	}
}

pub(crate) fn register_metrics<T: PrometheusRegister>(
	prometheus_registry: Option<prometheus::Registry>,
) -> Option<T> {
	prometheus_registry.as_ref().map(T::register).and_then(|result| match result {
		Ok(metrics) => {
			debug!(target: "beefy", "🥩 Registered {} metrics", T::DESCRIPTION);
			Some(metrics)
		},
		Err(err) => {
			debug!(target: "beefy", "🥩 Failed to register {} metrics: {:?}", T::DESCRIPTION, err);
			None
		},
	})
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

#[macro_export]
macro_rules! metric_get {
	($self:ident, $m:ident) => {{
		$self.metrics.as_ref().map(|metrics| metrics.$m.clone())
	}};
}
