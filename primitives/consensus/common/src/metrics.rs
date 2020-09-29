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

//! Metering tools for consensus

use prometheus_endpoint::{
	register, U64, Registry, PrometheusError, Opts, CounterVec, Histogram, HistogramVec, HistogramOpts
};

use sp_runtime::traits::{Block as BlockT, NumberFor};

use crate::import_queue::{BlockImportResult, BlockImportError};

/// Generic Prometheus metrics for common consensus functionality.
#[derive(Clone)]
pub(crate) struct Metrics {
	pub import_queue_processed: CounterVec<U64>,
	pub block_verification_time: HistogramVec,
	pub block_verification_and_import_time: Histogram,
	pub finality_proof_import_time: Histogram,
	pub justification_import_time: Histogram,
}

impl Metrics {
	pub(crate) fn register(registry: &Registry) -> Result<Self, PrometheusError> {
		Ok(Self {
			import_queue_processed: register(
				CounterVec::new(
					Opts::new("import_queue_processed_total", "Blocks processed by import queue"),
					&["result"] // 'success or failure
				)?,
				registry,
			)?,
			block_verification_time: register(
				HistogramVec::new(
					HistogramOpts::new(
						"block_verification_time",
						"Time taken to verify blocks",
					),
					&["result"],
				)?,
				registry,
			)?,
			block_verification_and_import_time: register(
				Histogram::with_opts(
					HistogramOpts::new(
						"block_verification_and_import_time",
						"Time taken to verify and import blocks",
					),
				)?,
				registry,
			)?,
			finality_proof_import_time: register(
				Histogram::with_opts(
					HistogramOpts::new(
						"finality_proof_import_time",
						"Time taken to import finality proofs",
					),
				)?,
				registry,
			)?,
			justification_import_time: register(
				Histogram::with_opts(
					HistogramOpts::new(
						"justification_import_time",
						"Time taken to import justifications",
					),
				)?,
				registry,
			)?,
		})
	}

	pub fn report_import<B: BlockT>(
		&self,
		result: &Result<BlockImportResult<NumberFor<B>>, BlockImportError>,
	) {
		let label = match result {
			Ok(_) => "success",
			Err(BlockImportError::IncompleteHeader(_)) => "incomplete_header",
			Err(BlockImportError::VerificationFailed(_,_)) => "verification_failed",
			Err(BlockImportError::BadBlock(_)) => "bad_block",
			Err(BlockImportError::MissingState) => "missing_state",
			Err(BlockImportError::UnknownParent) => "unknown_parent",
			Err(BlockImportError::Cancelled) => "cancelled",
			Err(BlockImportError::Other(_)) => "failed",
		};

		self.import_queue_processed.with_label_values(
			&[label]
		).inc();
	}

	pub fn report_verification(&self, success: bool, time: std::time::Duration) {
		self.block_verification_time.with_label_values(
			&[if success { "success" } else { "verification_failed" }]
		).observe(time.as_secs_f64());
	}

	pub fn report_verification_and_import(&self, time: std::time::Duration) {
		self.block_verification_and_import_time.observe(time.as_secs_f64());
	}
}
