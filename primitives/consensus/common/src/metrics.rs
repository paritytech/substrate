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

use prometheus_endpoint::{register, CounterVec, Opts, PrometheusError, Registry, U64};

/// Generic Prometheus metrics for common consensus functionality.
#[derive(Clone)]
pub(crate) struct Metrics {
    pub import_queue_processed: CounterVec<U64>,
}

impl Metrics {
    pub(crate) fn register(registry: &Registry) -> Result<Self, PrometheusError> {
        Ok(Self {
            import_queue_processed: register(
                CounterVec::new(
                    Opts::new(
                        "import_queue_processed_total",
                        "Blocks processed by import queue",
                    ),
                    &["result"], // 'success or failure
                )?,
                registry,
            )?,
        })
    }
}
