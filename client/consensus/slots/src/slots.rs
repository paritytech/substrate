// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Utility stream for yielding slots in a loop.
//!
//! This is used instead of `futures_timer::Interval` because it was unreliable.

use super::{SlotCompatible, Slot};
use sp_consensus::Error;
use sp_inherents::{InherentData, InherentDataProviders};

use std::time::{Duration, Instant};
use futures_timer::Delay;

/// Returns current duration since unix epoch.
pub fn duration_now() -> Duration {
	use std::time::SystemTime;
	let now = SystemTime::now();
	now.duration_since(SystemTime::UNIX_EPOCH).unwrap_or_else(|e| panic!(
		"Current time {:?} is before unix epoch. Something is wrong: {:?}",
		now,
		e,
	))
}

/// Returns the duration until the next slot, based on current duration since
pub fn time_until_next(now: Duration, slot_duration: Duration) -> Duration {
	let remaining_full_millis = slot_duration.as_millis()
		- (now.as_millis() % slot_duration.as_millis())
		- 1;
	Duration::from_millis(remaining_full_millis as u64)
}

/// Information about a slot.
pub struct SlotInfo {
	/// The slot number.
	pub slot: Slot,
	/// Current timestamp.
	pub timestamp: sp_timestamp::Timestamp,
	/// The instant at which the slot ends.
	pub ends_at: Instant,
	/// The inherent data.
	pub inherent_data: InherentData,
	/// Slot duration.
	pub duration: Duration,
}

impl SlotInfo {
	/// Create a new [`SlotInfo`].
	///
	/// `ends_at` is calculated using `timestamp` and `duration`.
	pub fn new(
		slot: Slot,
		timestamp: sp_timestamp::Timestamp,
		inherent_data: InherentData,
		duration: Duration,
	) -> Self {
		Self {
			slot,
			timestamp,
			inherent_data,
			duration,
			ends_at: Instant::now() + time_until_next(timestamp.as_duration(), duration),
		}
	}
}

/// A stream that returns every time there is a new slot.
pub(crate) struct Slots<SC> {
	last_slot: Slot,
	slot_duration: Duration,
	inner_delay: Option<Delay>,
	inherent_data_providers: InherentDataProviders,
	timestamp_extractor: SC,
}

impl<SC> Slots<SC> {
	/// Create a new `Slots` stream.
	pub fn new(
		slot_duration: Duration,
		inherent_data_providers: InherentDataProviders,
		timestamp_extractor: SC,
	) -> Self {
		Slots {
			last_slot: 0.into(),
			slot_duration,
			inner_delay: None,
			inherent_data_providers,
			timestamp_extractor,
		}
	}
}

impl<SC: SlotCompatible> Slots<SC> {
	/// Returns a future that fires when the next slot starts.
	pub async fn next_slot(&mut self) -> Result<SlotInfo, Error> {
		loop {
			self.inner_delay = match self.inner_delay.take() {
				None => {
					// schedule wait.
					let wait_dur = time_until_next(duration_now(), self.slot_duration);
					Some(Delay::new(wait_dur))
				}
				Some(d) => Some(d),
			};

			if let Some(inner_delay) = self.inner_delay.take() {
				inner_delay.await;
			}
			// timeout has fired.

			let inherent_data = match self.inherent_data_providers.create_inherent_data() {
				Ok(id) => id,
				Err(err) => return Err(sp_consensus::Error::InherentData(err)),
			};
			let result = self.timestamp_extractor.extract_timestamp_and_slot(&inherent_data);
			let (timestamp, slot, offset) = match result {
				Ok(v) => v,
				Err(err) => return Err(err),
			};
			// reschedule delay for next slot.
			let ends_in = offset +
				time_until_next(timestamp.as_duration(), self.slot_duration);
			self.inner_delay = Some(Delay::new(ends_in));

			// never yield the same slot twice.
			if slot > self.last_slot {
				self.last_slot = slot;

				break Ok(SlotInfo::new(
					slot,
					timestamp,
					inherent_data,
					self.slot_duration,
				))
			}
		}
	}
}
