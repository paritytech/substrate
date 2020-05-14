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
//!
//! These are the metrics measured by consensus internals. These are
//! exposed publicly for two reasons: if you choose to not reuse the
//! existing BasicImportQueue, you can still use the same single
//! measuring component –– but you also have to do that tracking yourself.
//!
//! Secondly, this only does the general tracking using Prometheus
//! Primitives, it **does not** actually register them with the prometheus
//! process or service. This is expected to be done from the outside.
//! If you are using sc-service, this is already done for you.

use prometheus_endpoint::{register, U64, Registry, PrometheusError, Opts, CounterVec};

/// generic prometheus metrics for common consensus functionality.
#[derive(Clone)]
pub(crate) struct Metrics {
	pub import_queue_processed: CounterVec<U64>,
}

impl Metrics {
	pub(crate) fn register(registry: &Registry) -> Result<Self, PrometheusError> {
		Ok(Self {
			import_queue_processed: register(
				CounterVec::new(
					Opts::new("import_queue_processed", "Blocks processed by import queue"),
					&["result"] // 'success or failure
				)?,
				registry,
			)?,
		})
	}
}
