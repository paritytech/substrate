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

use super::InherentDataProviderExt;
use sp_consensus::{Error, SelectChain};
use futures::{prelude::*, task::Context, task::Poll};
use sp_inherents::{InherentData, CreateInherentDataProviders, InherentDataProvider};
use sp_runtime::{traits::{Block as BlockT, Header as HeaderT}, generic::BlockId};

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
pub fn time_until_next(now: Duration, slot_duration: u64) -> Duration {
	let remaining_full_millis = slot_duration - (now.as_millis() as u64 % slot_duration) - 1;
	Duration::from_millis(remaining_full_millis)
}

/// Information about a slot.
pub struct SlotInfo<B: BlockT> {
	/// The slot number.
	pub number: crate::Slot,
	/// Current timestamp.
	pub timestamp: Duration,
	/// The instant at which the slot ends.
	pub ends_at: Instant,
	/// The inherent data.
	pub inherent_data: InherentData,
	/// Slot duration.
	pub duration: u64,
	/// The chain header this slot is based on.
	pub chain_head: B::Header,
}

/// A stream that returns every time there is a new slot.
pub(crate) struct Slots<Block, C, IDP> {
	last_slot: crate::Slot,
	slot_duration: u64,
	inner_delay: Option<Delay>,
	inherent_data_providers: IDP,
	client: C,
	_phantom: std::marker::PhantomData<Block>,
}

impl<Block, C, IDP> Slots<Block, C, IDP> {
	/// Create a new `Slots` stream.
	pub fn new(
		slot_duration: u64,
		inherent_data_providers: IDP,
		client: C,
	) -> Self {
		Slots {
			last_slot: crate::Slot(0),
			slot_duration,
			inner_delay: None,
			inherent_data_providers,
			client,
			_phantom: Default::default(),
		}
	}
}

impl<Block, C, IDP> Stream for Slots<Block, C, IDP>
where
	Block: BlockT,
	C: SelectChain<Block>,
	IDP: CreateInherentDataProviders<Block, ()>,
	IDP::InherentDataProviders: crate::InherentDataProviderExt,
IDP::Error: Into<Error>,
{
	type Item = Result<SlotInfo<Block>, Error>;

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

			let chain_head = match self.client.best_chain() {
				Ok(x) => x,
				Err(e) => {
					log::warn!(
						target: "slots",
						"Unable to author block in slot. No best block header: {:?}",
						e,
					);
					// Let's try at the next slot..
					self.inner_delay.take();
					continue;
				}
			};

			let inherent_data_providers = match self.inherent_data_providers
				.create_inherent_data_providers(&BlockId::Hash(chain_head.hash()), ())
			{
				Ok(id) => id,
				Err(err) => return Poll::Ready(Some(Err(err.into()))),
			};

			let timestamp = inherent_data_providers.timestamp();
			let slot_num = inherent_data_providers.slot();
			let inherent_data = match inherent_data_providers.create_inherent_data() {
				Ok(d) => d,
				Err(err) => return Poll::Ready(Some(Err(err.into()))),
			};

			// reschedule delay for next slot.
			let ends_in = time_until_next(timestamp, slot_duration);
			let ends_at = Instant::now() + ends_in;
			self.inner_delay = Some(Delay::new(ends_in));

			// never yield the same slot twice.
			if slot_num > self.last_slot {
				self.last_slot = slot_num;

				break Poll::Ready(Some(Ok(SlotInfo {
					number: slot_num,
					duration: self.slot_duration,
					timestamp,
					ends_at,
					inherent_data,
					chain_head,
				})))
			}
		}
	}
}

impl<Block, C, IDP> Unpin for Slots<Block, C, IDP> {}
