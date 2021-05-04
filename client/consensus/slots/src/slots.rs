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

use super::{Slot, InherentDataProviderExt};
use sp_consensus::{Error, SelectChain};
use sp_inherents::{InherentData, CreateInherentDataProviders, InherentDataProvider};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};

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

/// Returns the duration until the next slot from now.
pub fn time_until_next(slot_duration: Duration) -> Duration {
	let remaining_full_millis = slot_duration.as_millis()
		- (duration_now().as_millis() % slot_duration.as_millis())
		- 1;
	Duration::from_millis(remaining_full_millis as u64)
}

/// Information about a slot.
pub struct SlotInfo<B: BlockT> {
	/// The slot number as found in the inherent data.
	pub slot: Slot,
	/// Current timestamp as found in the inherent data.
	pub timestamp: sp_timestamp::Timestamp,
	/// The instant at which the slot ends.
	pub ends_at: Instant,
	/// The inherent data.
	pub inherent_data: InherentData,
	/// Slot duration.
	pub duration: Duration,
	/// The chain header this slot is based on.
	pub chain_head: B::Header,
	/// Some potential block size limit for the block to be authored at this slot.
	///
	/// For more information see [`Proposer::propose`](sp_consensus::Proposer::propose).
	pub block_size_limit: Option<usize>,
}

impl<B: BlockT> SlotInfo<B> {
	/// Create a new [`SlotInfo`].
	///
	/// `ends_at` is calculated using `timestamp` and `duration`.
	pub fn new(
		slot: Slot,
		timestamp: sp_timestamp::Timestamp,
		inherent_data: InherentData,
		duration: Duration,
		chain_head: B::Header,
		block_size_limit: Option<usize>,
	) -> Self {
		Self {
			slot,
			timestamp,
			inherent_data,
			duration,
			chain_head,
			block_size_limit,
			ends_at: Instant::now() + time_until_next(duration),
		}
	}
}

/// A stream that returns every time there is a new slot.
pub(crate) struct Slots<Block, C, IDP> {
	last_slot: Slot,
	slot_duration: Duration,
	inner_delay: Option<Delay>,
	create_inherent_data_providers: IDP,
	client: C,
	_phantom: std::marker::PhantomData<Block>,
}

impl<Block, C, IDP> Slots<Block, C, IDP> {
	/// Create a new `Slots` stream.
	pub fn new(
		slot_duration: Duration,
		create_inherent_data_providers: IDP,
		client: C,
	) -> Self {
		Slots {
			last_slot: 0.into(),
			slot_duration,
			inner_delay: None,
			create_inherent_data_providers,
			client,
			_phantom: Default::default(),
		}
	}
}

impl<Block, C, IDP> Slots<Block, C, IDP>
where
	Block: BlockT,
	C: SelectChain<Block>,
	IDP: CreateInherentDataProviders<Block, ()>,
	IDP::InherentDataProviders: crate::InherentDataProviderExt,
{
	/// Returns a future that fires when the next slot starts.
	pub async fn next_slot(&mut self) -> Result<SlotInfo<Block>, Error> {
		loop {
			self.inner_delay = match self.inner_delay.take() {
				None => {
					// schedule wait.
					let wait_dur = time_until_next(self.slot_duration);
					Some(Delay::new(wait_dur))
				}
				Some(d) => Some(d),
			};

			if let Some(inner_delay) = self.inner_delay.take() {
				inner_delay.await;
			}
			// timeout has fired.

			let ends_at = Instant::now() + time_until_next(self.slot_duration);

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

			let inherent_data_providers = self.create_inherent_data_providers
				.create_inherent_data_providers(chain_head.hash(), ())
				.await?;

			if Instant::now() > ends_at {
				log::warn!(
					target: "slots",
					"Creating inherent data providers took more time than we had left for the slot.",
				);
			}

			let timestamp = inherent_data_providers.timestamp();
			let slot = inherent_data_providers.slot();
			let inherent_data = inherent_data_providers.create_inherent_data()?;

			// reschedule delay for next slot.
			let ends_in = time_until_next(self.slot_duration);
			self.inner_delay = Some(Delay::new(ends_in));

			// never yield the same slot twice.
			if slot > self.last_slot {
				self.last_slot = slot;

				break Ok(SlotInfo::new(
					slot,
					timestamp,
					inherent_data,
					self.slot_duration,
					chain_head,
					None,
				))
			}
		}
	}
}
