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

//! Slots functionality for Substrate.
//!
//! Some consensus algorithms have a concept of *slots*, which are intervals in
//! time during which certain events can and/or must occur.  This crate
//! provides generic functionality for slots.

#![deny(warnings)]
#![forbid(unsafe_code, missing_docs)]

mod slots;
mod aux_schema;

pub use slots::{SignedDuration, SlotInfo};
use slots::Slots;
pub use aux_schema::{check_equivocation, MAX_SLOT_CAPACITY, PRUNING_BOUND};

use codec::{Decode, Encode};
use consensus_common::{SyncOracle, SelectChain};
use futures::{prelude::*, future::{self, Either}};
use inherents::{InherentData, InherentDataProviders};
use log::{debug, error, info, warn};
use sr_primitives::generic::BlockId;
use sr_primitives::traits::{ApiRef, Block as BlockT, ProvideRuntimeApi};
use std::{fmt::Debug, ops::Deref};

/// A worker that should be invoked at every new slot.
pub trait SlotWorker<B: BlockT> {
	/// The type of the future that will be returned when a new slot is
	/// triggered.
	type OnSlot: Future<Output = Result<(), consensus_common::Error>>;

	/// Called when a new slot is triggered.
	fn on_slot(&mut self, chain_head: B::Header, slot_info: SlotInfo) -> Self::OnSlot;
}

/// Slot compatible inherent data.
pub trait SlotCompatible {
	/// Extract timestamp and slot from inherent data.
	fn extract_timestamp_and_slot(
		&self,
		inherent: &InherentData,
	) -> Result<(u64, u64, std::time::Duration), consensus_common::Error>;

	/// Get the difference between chain time and local time.  Defaults to
	/// always returning zero.
	fn time_offset() -> SignedDuration { Default::default() }
}

/// Start a new slot worker.
///
/// Every time a new slot is triggered, `worker.on_slot` is called and the future it returns is
/// polled until completion, unless we are major syncing.
pub fn start_slot_worker<B, C, W, T, SO, SC>(
	slot_duration: SlotDuration<T>,
	client: C,
	mut worker: W,
	mut sync_oracle: SO,
	inherent_data_providers: InherentDataProviders,
	timestamp_extractor: SC,
) -> impl Future<Output = ()>
where
	B: BlockT,
	C: SelectChain<B> + Clone,
	W: SlotWorker<B>,
	W::OnSlot: Unpin,
	SO: SyncOracle + Send + Clone,
	SC: SlotCompatible + Unpin,
	T: SlotData + Clone,
{
	let SlotDuration(slot_duration) = slot_duration;

	// rather than use a timer interval, we schedule our waits ourselves
	Slots::<SC>::new(
		slot_duration.slot_duration(),
		inherent_data_providers,
		timestamp_extractor,
	).inspect_err(|e| debug!(target: "slots", "Faulty timer: {:?}", e))
		.try_for_each(move |slot_info| {
			// only propose when we are not syncing.
			if sync_oracle.is_major_syncing() {
				debug!(target: "slots", "Skipping proposal slot due to sync.");
				return Either::Right(future::ready(Ok(())));
			}

			let slot_num = slot_info.number;
			let chain_head = match client.best_chain() {
				Ok(x) => x,
				Err(e) => {
					warn!(target: "slots", "Unable to author block in slot {}. \
					no best block header: {:?}", slot_num, e);
					return Either::Right(future::ready(Ok(())));
				}
			};

			Either::Left(worker.on_slot(chain_head, slot_info).map_err(
				|e| {
					warn!(target: "slots", "Encountered consensus error: {:?}", e);
				}).or_else(|_| future::ready(Ok(())))
			)
		}).then(|res| {
			if let Err(err) = res {
				warn!(target: "slots", "Slots stream terminated with an error: {:?}", err);
			}
			future::ready(())
		})
}

/// A header which has been checked
pub enum CheckedHeader<H, S> {
	/// A header which has slot in the future. this is the full header (not stripped)
	/// and the slot in which it should be processed.
	Deferred(H, u64),
	/// A header which is fully checked, including signature. This is the pre-header
	/// accompanied by the seal components.
	///
	/// Includes the digest item that encoded the seal.
	Checked(H, S),
}

/// A type from which a slot duration can be obtained.
pub trait SlotData {
	/// Gets the slot duration.
	fn slot_duration(&self) -> u64;

	/// The static slot key
	const SLOT_KEY: &'static [u8];
}

impl SlotData for u64 {
	fn slot_duration(&self) -> u64 {
		*self
	}

	const SLOT_KEY: &'static [u8] = b"aura_slot_duration";
}

/// A slot duration. Create with `get_or_compute`.
// The internal member should stay private here.
#[derive(Clone, Copy, Debug, Encode, Decode, Hash, PartialOrd, Ord, PartialEq, Eq)]
pub struct SlotDuration<T>(T);

impl<T> Deref for SlotDuration<T> {
	type Target = T;
	fn deref(&self) -> &T {
		&self.0
	}
}

impl<T: SlotData + Clone> SlotData for SlotDuration<T> {
	/// Get the slot duration in milliseconds.
	fn slot_duration(&self) -> u64
		where T: SlotData,
	{
		self.0.slot_duration()
	}

	const SLOT_KEY: &'static [u8] = T::SLOT_KEY;
}

impl<T: Clone> SlotDuration<T> {
	/// Either fetch the slot duration from disk or compute it from the
	/// genesis state.
	///
	/// `slot_key` is marked as `'static`, as it should really be a
	/// compile-time constant.
	pub fn get_or_compute<B: BlockT, C, CB>(client: &C, cb: CB) -> ::client::error::Result<Self> where
		C: client::backend::AuxStore,
		C: ProvideRuntimeApi,
		CB: FnOnce(ApiRef<C::Api>, &BlockId<B>) -> ::client::error::Result<T>,
		T: SlotData + Encode + Decode + Debug,
	{
		match client.get_aux(T::SLOT_KEY)? {
			Some(v) => <T as codec::Decode>::decode(&mut &v[..])
				.map(SlotDuration)
				.ok_or_else(|| {
					::client::error::Error::Backend({
						error!(target: "slots", "slot duration kept in invalid format");
						format!("slot duration kept in invalid format")
					})
					.into()
				}),
			None => {
				use sr_primitives::traits::Zero;
				let genesis_slot_duration =
					cb(client.runtime_api(), &BlockId::number(Zero::zero()))?;

				info!(
					"Loaded block-time = {:?} seconds from genesis on first-launch",
					genesis_slot_duration
				);

				genesis_slot_duration
					.using_encoded(|s| client.insert_aux(&[(T::SLOT_KEY, &s[..])], &[]))?;

				Ok(SlotDuration(genesis_slot_duration))
			}
		}
	}

	/// Returns slot data value.
	pub fn get(&self) -> T {
		self.0.clone()
	}
}
