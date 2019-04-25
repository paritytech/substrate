// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Utility stream for yielding slots in a loop.
//!
//! This is used instead of `tokio_timer::Interval` because it was unreliable.

use std::time::{Instant, Duration};
use std::marker::PhantomData;
use tokio::timer::Delay;
use futures::prelude::*;
use futures::try_ready;
use log::warn;
use inherents::{InherentDataProviders, InherentData};
use consensus_common::{Error, ErrorKind};
use crate::SlotCompatible;

/// Returns current duration since unix epoch.
pub fn duration_now() -> Option<Duration> {
	use std::time::SystemTime;

	let now = SystemTime::now();
	now.duration_since(SystemTime::UNIX_EPOCH).map_err(|e| {
		warn!("Current time {:?} is before unix epoch. Something is wrong: {:?}", now, e);
	}).ok()
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
			try_ready!(inner_delay.poll().map_err(|e| Error::from(ErrorKind::FaultyTimer(e))));
		}

		// timeout has fired.

		let inherent_data = self.inherent_data_providers.create_inherent_data()
			.map_err(crate::inherent_to_common_error)?;
		let (timestamp, slot_num) = SC::extract_timestamp_and_slot(&inherent_data)?;

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
						duration: self.slot_duration,
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
