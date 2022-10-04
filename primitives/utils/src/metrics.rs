// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Metering primitives and globals

use lazy_static::lazy_static;
use prometheus::{
	core::{AtomicU64, GenericCounter, GenericGauge},
	Error as PrometheusError, Registry,
};

#[cfg(feature = "metered")]
use prometheus::{core::GenericCounterVec, Opts};

lazy_static! {
	pub static ref TOKIO_THREADS_TOTAL: GenericCounter<AtomicU64> =
		GenericCounter::new("tokio_threads_total", "Total number of threads created")
			.expect("Creating of statics doesn't fail. qed");
	pub static ref TOKIO_THREADS_ALIVE: GenericGauge<AtomicU64> =
		GenericGauge::new("tokio_threads_alive", "Number of threads alive right now")
			.expect("Creating of statics doesn't fail. qed");
}

#[cfg(feature = "metered")]
lazy_static! {
	pub static ref UNBOUNDED_CHANNELS_COUNTER : GenericCounterVec<AtomicU64> = GenericCounterVec::new(
		Opts::new("unbounded_channel_len", "Items in each mpsc::unbounded instance"),
		&["entity", "action"] // 'name of channel, send|received|dropped
	).expect("Creating of statics doesn't fail. qed");

}

/// Register the statics to report to registry
pub fn register_globals(registry: &Registry) -> Result<(), PrometheusError> {
	registry.register(Box::new(TOKIO_THREADS_ALIVE.clone()))?;
	registry.register(Box::new(TOKIO_THREADS_TOTAL.clone()))?;

	#[cfg(feature = "metered")]
	registry.register(Box::new(UNBOUNDED_CHANNELS_COUNTER.clone()))?;

	Ok(())
}
