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

//! Metering primitives and globals

use lazy_static::lazy_static;
use prometheus::{
	Registry, Error as PrometheusError,
	core::{ AtomicU64, GenericGauge, GenericCounter },
};

#[cfg(features = "metered")]
use prometheus::{core::GenericGaugeVec, Opts};


lazy_static! {
	pub static ref TOKIO_THREADS_TOTAL: GenericCounter<AtomicU64> = GenericCounter::new(
		"tokio_threads_total", "Total number of threads created"
	).expect("Creating of statics doesn't fail. qed");

	pub static ref TOKIO_THREADS_ALIVE: GenericGauge<AtomicU64> = GenericGauge::new(
		"tokio_threads_alive", "Number of threads alive right now"
	).expect("Creating of statics doesn't fail. qed");
}

#[cfg(features = "metered")]
lazy_static! {
	pub static ref UNBOUNDED_CHANNELS_COUNTER : GenericGaugeVec<AtomicU64> = GenericGaugeVec::new(
		Opts::new("unbounded_channel_len", "Items in each mpsc::unbounded instance"),
		&["entity", "action"] // 'name of channel, send|received|dropped
	).expect("Creating of statics doesn't fail. qed");

}


/// Register the statics to report to registry
pub fn register_globals(registry: &Registry) -> Result<(), PrometheusError> {
	registry.register(Box::new(TOKIO_THREADS_ALIVE.clone()))?;
	registry.register(Box::new(TOKIO_THREADS_TOTAL.clone()))?;

	#[cfg(features = "metered")]
	registry.register(Box::new(UNBOUNDED_CHANNELS_COUNTER.clone()))?;

	Ok(())
}
