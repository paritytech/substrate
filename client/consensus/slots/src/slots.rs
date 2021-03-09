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
	pub timestamp: u64,
	/// The instant at which the slot ends.
	pub ends_at: Instant,
	/// The inherent data.
	pub inherent_data: InherentData,
	/// Slot duration.
	pub duration: Duration,
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
		slot_duration: u64,
		inherent_data_providers: InherentDataProviders,
		timestamp_extractor: SC,
	) -> Self {
		Slots {
			last_slot: 0.into(),
			slot_duration: Duration::from_millis(slot_duration),
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
			let (timestamp, slot, offset) = match result {
				Ok(v) => v,
				Err(err) => return Poll::Ready(Some(Err(err))),
			};
			// reschedule delay for next slot.
			let ends_in = offset +
				time_until_next(Duration::from_millis(timestamp), slot_duration);
			let ends_at = Instant::now() + ends_in;
			self.inner_delay = Some(Delay::new(ends_in));

			// never yield the same slot twice.
			if slot > self.last_slot {
				self.last_slot = slot;

				break Poll::Ready(Some(Ok(SlotInfo {
					slot,
					duration: self.slot_duration,
					timestamp,
					ends_at,
					inherent_data,
				})))
			}
		}
	}
}

impl<SC> Unpin for Slots<SC> {}
