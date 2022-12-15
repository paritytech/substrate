// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

use prometheus_endpoint::{
	prometheus::CounterVec, register, Gauge, Histogram, HistogramOpts, Opts, PrometheusError,
	Registry, U64,
};

/// Optional shareable link to basic authorship metrics.
#[derive(Clone, Default)]
pub struct MetricsLink(Option<Metrics>);

impl MetricsLink {
	pub fn new(registry: Option<&Registry>) -> Self {
		Self(registry.and_then(|registry| {
			Metrics::register(registry)
				.map_err(|err| {
					log::warn!("Failed to register proposer prometheus metrics: {}", err)
				})
				.ok()
		}))
	}

	pub fn report<O>(&self, do_this: impl FnOnce(&Metrics) -> O) -> Option<O> {
		self.0.as_ref().map(do_this)
	}
}

/// The reason why proposing a block ended.
pub enum EndProposingReason {
	NoMoreTransactions,
	HitDeadline,
	HitBlockSizeLimit,
	HitBlockWeightLimit,
}

/// Authorship metrics.
#[derive(Clone)]
pub struct Metrics {
	pub block_constructed: Histogram,
	pub number_of_transactions: Gauge<U64>,
	pub end_proposing_reason: CounterVec,
	pub create_inherents_time: Histogram,
	pub create_block_proposal_time: Histogram,
}

impl Metrics {
	pub fn register(registry: &Registry) -> Result<Self, PrometheusError> {
		Ok(Self {
			block_constructed: register(
				Histogram::with_opts(HistogramOpts::new(
					"substrate_proposer_block_constructed",
					"Histogram of time taken to construct new block",
				))?,
				registry,
			)?,
			number_of_transactions: register(
				Gauge::new(
					"substrate_proposer_number_of_transactions",
					"Number of transactions included in block",
				)?,
				registry,
			)?,
			create_inherents_time: register(
				Histogram::with_opts(HistogramOpts::new(
					"substrate_proposer_create_inherents_time",
					"Histogram of time taken to execute create inherents",
				))?,
				registry,
			)?,
			create_block_proposal_time: register(
				Histogram::with_opts(HistogramOpts::new(
					"substrate_proposer_block_proposal_time",
					"Histogram of time taken to construct a block and prepare it for proposal",
				))?,
				registry,
			)?,
			end_proposing_reason: register(
				CounterVec::new(
					Opts::new(
						"substrate_proposer_end_proposal_reason",
						"The reason why the block proposing was ended. This doesn't include errors.",
					),
					&["reason"],
				)?,
				registry,
			)?,
		})
	}

	/// Report the reason why the proposing ended.
	pub fn report_end_proposing_reason(&self, reason: EndProposingReason) {
		let reason = match reason {
			EndProposingReason::HitDeadline => "hit_deadline",
			EndProposingReason::NoMoreTransactions => "no_more_transactions",
			EndProposingReason::HitBlockSizeLimit => "hit_block_size_limit",
			EndProposingReason::HitBlockWeightLimit => "hit_block_weight_limit",
		};

		self.end_proposing_reason.with_label_values(&[reason]).inc();
	}
}
