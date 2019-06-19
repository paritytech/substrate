// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Utility stream for yielding slots in a loop.
//!
//! This is used instead of `tokio_timer::Interval` because it was unreliable.

use super::SlotCompatible;
use consensus_common::Error;
use futures::prelude::*;
use futures::try_ready;
use inherents::{InherentData, InherentDataProviders};
use log::warn;
use std::marker::PhantomData;
use std::time::{Duration, Instant};
use tokio_timer::Delay;

/// Returns current duration since unix epoch.
pub fn duration_now() -> Option<Duration> {
	use std::time::SystemTime;

	let now = SystemTime::now();
	now.duration_since(SystemTime::UNIX_EPOCH)
		.map_err(|e| {
			warn!(
				"Current time {:?} is before unix epoch. Something is wrong: {:?}",
				now, e
			);
		})
		.ok()
}

/// Get the slot for now.
pub fn slot_now(slot_duration: u64) -> Option<u64> {
	duration_now().map(|s| s.as_secs() / slot_duration)
}

/// Returns the duration until the next slot, based on current duration since
pub fn time_until_next(now: Duration, slot_duration: u64) -> Duration {
	let remaining_full_secs = slot_duration - (now.as_secs() % slot_duration) - 1;
	let remaining_nanos = 1_000_000_000 - now.subsec_nanos();
	Duration::new(remaining_full_secs, remaining_nanos)
}

/// Information about a slot.
pub struct SlotInfo {
	/// The slot number.
	pub number: u64,
	/// Current timestamp.
	pub timestamp: u64,
	/// The instant at which the slot ends.
	pub ends_at: Instant,
	/// The inherent data.
	pub inherent_data: InherentData,
	/// Slot duration.
	pub duration: u64,
}

impl SlotInfo {
	/// Yields the remaining duration in the slot.
	pub fn remaining_duration(&self) -> Duration {
		let now = Instant::now();
		if now < self.ends_at {
			self.ends_at.duration_since(now)
		} else {
			Duration::from_secs(0)
		}
	}
}

/// A stream that returns every time there is a new slot.
pub struct Slots<SC> {
	last_slot: u64,
	slot_duration: u64,
	inner_delay: Option<Delay>,
	inherent_data_providers: InherentDataProviders,
	_marker: PhantomData<SC>,
}

impl<SC> Slots<SC> {
	/// Create a new `Slots` stream.
	pub fn new(slot_duration: u64, inherent_data_providers: InherentDataProviders) -> Self {
		Slots {
			last_slot: 0,
			slot_duration,
			inner_delay: None,
			inherent_data_providers,
			_marker: PhantomData,
		}
	}
}

impl<SC: SlotCompatible> Stream for Slots<SC> {
	type Item = SlotInfo;
	type Error = Error;

	fn poll(&mut self) -> Poll<Option<SlotInfo>, Self::Error> {
		let slot_duration = self.slot_duration;
		self.inner_delay = match self.inner_delay.take() {
			None => {
				// schedule wait.
				let wait_until = match duration_now() {
					None => return Ok(Async::Ready(None)),
					Some(now) => Instant::now() + time_until_next(now, slot_duration),
				};

				Some(Delay::new(wait_until))
			}
			Some(d) => Some(d),
		};

		if let Some(ref mut inner_delay) = self.inner_delay {
			try_ready!(inner_delay
				.poll()
				.map_err(Error::FaultyTimer));
		}

		// timeout has fired.

		let inherent_data = self
			.inherent_data_providers
			.create_inherent_data()
			.map_err(|s| consensus_common::Error::InherentData(s.into_owned()))?;
		let (timestamp, slot_num) = SC::extract_timestamp_and_slot(&inherent_data)?;

		// reschedule delay for next slot.
		let ends_at =
			Instant::now() + time_until_next(Duration::from_secs(timestamp), slot_duration);
		self.inner_delay = Some(Delay::new(ends_at));

		// never yield the same slot twice.
		if slot_num > self.last_slot {
			self.last_slot = slot_num;

			Ok(Async::Ready(Some(SlotInfo {
				number: slot_num,
				duration: self.slot_duration,
				timestamp,
				ends_at,
				inherent_data,
			})))
		} else {
			// re-poll until we get a new slot.
			self.poll()
		}
	}
}
