// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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
//! This is used instead of `futures_timer::Interval` because it was unreliable.

use super::SlotCompatible;
use sp_consensus::Error;
use futures::{prelude::*, task::Context, task::Poll};
use sp_inherents::{InherentData, InherentDataProviders};

use std::{pin::Pin, time::{Duration, Instant}};
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


/// A `Duration` with a sign (before or after).  Immutable.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct SignedDuration {
	offset: Duration,
	is_positive: bool,
}

impl SignedDuration {
	/// Construct a `SignedDuration`
	pub fn new(offset: Duration, is_positive: bool) -> Self {
		Self { offset, is_positive }
	}

	/// Get the slot for now.  Panics if `slot_duration` is 0.
	pub fn slot_now(&self, slot_duration: u64) -> u64 {
		(if self.is_positive {
			duration_now() + self.offset
		} else {
			duration_now() - self.offset
		}.as_millis() as u64) / slot_duration
	}
}

/// Returns the duration until the next slot, based on current duration since
pub fn time_until_next(now: Duration, slot_duration: u64) -> Duration {
	let remaining_full_millis = slot_duration - (now.as_millis() as u64 % slot_duration) - 1;
	Duration::from_millis(remaining_full_millis)
}

/// Information about a slot.
pub struct SlotInfo {
	/// The slot number.
	pub number: u64,
	/// The last slot number produced.
	pub last_number: u64,
	/// Current timestamp.
	pub timestamp: u64,
	/// The instant at which the slot ends.
	pub ends_at: Instant,
	/// The inherent data.
	pub inherent_data: InherentData,
	/// Slot duration.
	pub duration: u64,
}

/// A stream that returns every time there is a new slot.
pub(crate) struct Slots<SC> {
	last_slot: u64,
	slot_duration: u64,
	inner_delay: Option<Delay>,
	inherent_data_providers: InherentDataProviders,
	timestamp_extractor: SC,
}

impl<SC> Slots<SC> {
	/// Create a new `Slots` stream.
	pub fn new(
		slot_duration: u64,
		inherent_data_providers: InherentDataProviders,
		timestamp_extractor: SC,
	) -> Self {
		Slots {
			last_slot: 0,
			slot_duration,
			inner_delay: None,
			inherent_data_providers,
			timestamp_extractor,
		}
	}
}

impl<SC: SlotCompatible> Stream for Slots<SC> {
	type Item = Result<SlotInfo, Error>;

	fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
		loop {
			let slot_duration = self.slot_duration;
			self.inner_delay = match self.inner_delay.take() {
				None => {
					// schedule wait.
					let wait_dur = time_until_next(duration_now(), slot_duration);
					Some(Delay::new(wait_dur))
				}
				Some(d) => Some(d),
			};

			if let Some(ref mut inner_delay) = self.inner_delay {
				match Future::poll(Pin::new(inner_delay), cx) {
					Poll::Pending => return Poll::Pending,
					Poll::Ready(()) => {}
				}
			}

			// timeout has fired.

			let inherent_data = match self.inherent_data_providers.create_inherent_data() {
				Ok(id) => id,
				Err(err) => return Poll::Ready(Some(Err(sp_consensus::Error::InherentData(err)))),
			};
			let result = self.timestamp_extractor.extract_timestamp_and_slot(&inherent_data);
			let (timestamp, slot_num, offset) = match result {
				Ok(v) => v,
				Err(err) => return Poll::Ready(Some(Err(err))),
			};
			// reschedule delay for next slot.
			let ends_in = offset +
				time_until_next(Duration::from_millis(timestamp), slot_duration);
			let ends_at = Instant::now() + ends_in;
			self.inner_delay = Some(Delay::new(ends_in));

			// never yield the same slot twice.
			if slot_num > self.last_slot {
				let last_slot = self.last_slot;
				self.last_slot = slot_num;

				break Poll::Ready(Some(Ok(SlotInfo {
					number: slot_num,
					duration: self.slot_duration,
					last_number: last_slot,
					timestamp,
					ends_at,
					inherent_data,
				})))
			}
		}
	}
}

impl<SC> Unpin for Slots<SC> {
}
