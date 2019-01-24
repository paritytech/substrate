// Copyright 2018 Parity Technologies (UK) Ltd.
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

use std::time::{Instant, Duration};
use tokio::timer::Delay;
use futures::prelude::*;
use futures::try_ready;

use inherents::{InherentDataProviders, InherentData};

use consensus_common::{Error, ErrorKind};

/// Returns the duration until the next slot, based on current duration since
pub(crate) fn time_until_next(now: Duration, slot_duration: u64) -> Duration {
	let remaining_full_secs = slot_duration - (now.as_secs() % slot_duration) - 1;
	let remaining_nanos = 1_000_000_000 - now.subsec_nanos();
	Duration::new(remaining_full_secs, remaining_nanos)
}

/// Information about a slot.
pub(crate) struct SlotInfo {
	/// The slot number.
	pub(crate) number: u64,
	/// Current timestamp.
	pub(crate) timestamp: u64,
	/// The instant at which the slot ends.
	pub(crate) ends_at: Instant,
	/// The inherent data.
	pub(crate) inherent_data: InherentData,
}

impl SlotInfo {
	/// Yields the remaining duration in the slot.
	pub(crate) fn remaining_duration(&self) -> Duration {
		let now = Instant::now();
		if now < self.ends_at {
			self.ends_at.duration_since(now)
		} else {
			Duration::from_secs(0)
		}
	}
}

/// A stream that returns every time there is a new slot.
pub(crate) struct Slots {
	last_slot: u64,
	slot_duration: u64,
	inner_delay: Option<Delay>,
	inherent_data_providers: InherentDataProviders,
}

impl Slots {
	/// Create a new `Slots` stream.
	pub(crate) fn new(slot_duration: u64, inherent_data_providers: InherentDataProviders) -> Self {
		Slots {
			last_slot: 0,
			slot_duration,
			inner_delay: None,
			inherent_data_providers,
		}
	}
}

impl Stream for Slots {
	type Item = SlotInfo;
	type Error = Error;

	fn poll(&mut self) -> Poll<Option<SlotInfo>, Self::Error> {
		let slot_duration = self.slot_duration;
		self.inner_delay = match self.inner_delay.take() {
			None => {
				// schedule wait.
				let wait_until = match crate::duration_now() {
					None => return Ok(Async::Ready(None)),
					Some(now) => Instant::now() + time_until_next(now, slot_duration),
				};

				Some(Delay::new(wait_until))
			}
			Some(d) => Some(d),
		};

		if let Some(ref mut inner_delay) = self.inner_delay {
			try_ready!(inner_delay.poll().map_err(|e| Error::from(ErrorKind::FaultyTimer(e))));
		}

		// timeout has fired.

		let inherent_data = self.inherent_data_providers.create_inherent_data()
			.map_err(crate::inherent_to_common_error)?;
		let (timestamp, slot_num) = crate::extract_timestamp_and_slot(&inherent_data)?;

		// reschedule delay for next slot.
		let ends_at = Instant::now() + time_until_next(Duration::from_secs(timestamp), slot_duration);
		self.inner_delay = Some(Delay::new(ends_at));

		// never yield the same slot twice.
		if slot_num > self.last_slot {
			self.last_slot = slot_num;

			Ok(
				Async::Ready(
					Some(SlotInfo {
						number: slot_num,
						timestamp,
						ends_at,
						inherent_data,
					})
				)
			)
		} else {
			// re-poll until we get a new slot.
			self.poll()
		}
	}
}
