// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

use super::{InherentDataProviderExt, Slot, LOG_TARGET};
use sp_consensus::{Error, SelectChain};
use sp_inherents::{CreateInherentDataProviders, InherentDataProvider};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};

use futures_timer::Delay;
use std::time::{Duration, Instant};

/// Returns current duration since unix epoch.
pub fn duration_now() -> Duration {
	use std::time::SystemTime;
	let now = SystemTime::now();
	now.duration_since(SystemTime::UNIX_EPOCH).unwrap_or_else(|e| {
		panic!("Current time {:?} is before unix epoch. Something is wrong: {:?}", now, e)
	})
}

/// Returns the duration until the next slot from now.
pub fn time_until_next_slot(slot_duration: Duration) -> Duration {
	let now = duration_now().as_millis();

	let next_slot = (now + slot_duration.as_millis()) / slot_duration.as_millis();
	let remaining_millis = next_slot * slot_duration.as_millis() - now;
	Duration::from_millis(remaining_millis as u64)
}

/// Information about a slot.
pub struct SlotInfo<B: BlockT> {
	/// The slot number as found in the inherent data.
	pub slot: Slot,
	/// The instant at which the slot ends.
	pub ends_at: Instant,
	/// The inherent data provider.
	pub create_inherent_data: Box<dyn InherentDataProvider>,
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
		create_inherent_data: Box<dyn InherentDataProvider>,
		duration: Duration,
		chain_head: B::Header,
		block_size_limit: Option<usize>,
	) -> Self {
		Self {
			slot,
			create_inherent_data,
			duration,
			chain_head,
			block_size_limit,
			ends_at: Instant::now() + time_until_next_slot(duration),
		}
	}
}

/// A stream that returns every time there is a new slot.
pub(crate) struct Slots<Block, SC, IDP> {
	last_slot: Slot,
	slot_duration: Duration,
	inner_delay: Option<Delay>,
	create_inherent_data_providers: IDP,
	select_chain: SC,
	_phantom: std::marker::PhantomData<Block>,
}

impl<Block, SC, IDP> Slots<Block, SC, IDP> {
	/// Create a new `Slots` stream.
	pub fn new(
		slot_duration: Duration,
		create_inherent_data_providers: IDP,
		select_chain: SC,
	) -> Self {
		Slots {
			last_slot: 0.into(),
			slot_duration,
			inner_delay: None,
			create_inherent_data_providers,
			select_chain,
			_phantom: Default::default(),
		}
	}
}

impl<Block, SC, IDP> Slots<Block, SC, IDP>
where
	Block: BlockT,
	SC: SelectChain<Block>,
	IDP: CreateInherentDataProviders<Block, ()> + 'static,
	IDP::InherentDataProviders: crate::InherentDataProviderExt,
{
	/// Returns a future that fires when the next slot starts.
	pub async fn next_slot(&mut self) -> Result<SlotInfo<Block>, Error> {
		loop {
			self.inner_delay = match self.inner_delay.take() {
				None => {
					// schedule wait.
					let wait_dur = time_until_next_slot(self.slot_duration);
					Some(Delay::new(wait_dur))
				},
				Some(d) => Some(d),
			};

			if let Some(inner_delay) = self.inner_delay.take() {
				inner_delay.await;
			}
			// timeout has fired.

			let ends_in = time_until_next_slot(self.slot_duration);

			// reschedule delay for next slot.
			self.inner_delay = Some(Delay::new(ends_in));
			let chain_head = match self.select_chain.best_chain().await {
				Ok(x) => x,
				Err(e) => {
					log::warn!(
						target: LOG_TARGET,
						"Unable to author block in slot. No best block header: {}",
						e,
					);
					// Let's try at the next slot..
					self.inner_delay.take();
					continue
				},
			};

			let inherent_data_providers = self
				.create_inherent_data_providers
				.create_inherent_data_providers(chain_head.hash(), ())
				.await?;

			let slot = inherent_data_providers.slot();

			// never yield the same slot twice.
			if slot > self.last_slot {
				self.last_slot = slot;

				break Ok(SlotInfo::new(
					slot,
					Box::new(inherent_data_providers),
					self.slot_duration,
					chain_head,
					None,
				))
			}
		}
	}
}
