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
use consensus_common::{BlockImport, Proposer, SyncOracle, SelectChain};
use futures::{prelude::*, future::{self, Either}};
use futures_timer::Delay;
use inherents::{InherentData, InherentDataProviders};
use log::{debug, error, info, warn};
use sr_primitives::generic::BlockId;
use sr_primitives::traits::{ApiRef, Block as BlockT, Header, ProvideRuntimeApi};
use std::{fmt::Debug, ops::Deref, pin::Pin, sync::Arc};
use substrate_telemetry::{telemetry, CONSENSUS_DEBUG, CONSENSUS_WARN, CONSENSUS_INFO};
use parking_lot::Mutex;

/// A worker that should be invoked at every new slot.
pub trait SlotWorker<B: BlockT> {
	/// The type of the future that will be returned when a new slot is
	/// triggered.
	type OnSlot: Future<Output = Result<(), consensus_common::Error>>;

	/// Called when a new slot is triggered.
	fn on_slot(&mut self, chain_head: B::Header, slot_info: SlotInfo) -> Self::OnSlot;
}

/// A skeleton implementation for `SlotWorker` which tries to claim a slot at at
/// its beginning and tries to produce a block if successfully claimed, timing
/// out if block production takes too long.
pub trait SimpleSlotWorker<B: BlockT> {
	/// A handle to a `BlockImport`.
	type BlockImport: BlockImport<B> + Send + 'static;

	/// A handle to a `SyncOracle`.
	type SyncOracle: SyncOracle;

	/// The type of proposer to use to build blocks.
	type Proposer: Proposer<B>;

	/// Data associated with a slot claim.
	type Claim: Send + 'static;

	/// Epoch data necessary for authoring.
	type EpochData;

	/// The logging target to use when logging messages.
	fn logging_target(&self) -> &'static str;

	/// A handle to a `BlockImport`.
	fn block_import(&self) -> Arc<Mutex<Self::BlockImport>>;

	/// Returns the epoch data necessary for authoring.
	fn epoch_data(&self, block: &B::Hash) -> Result<Self::EpochData, consensus_common::Error>;

	/// Returns the number of authorities given the epoch data.
	fn authorities_len(&self, epoch_data: &Self::EpochData) -> usize;

	/// Tries to claim the given slot, returning an object with claim data if successful.
	fn claim_slot(
		&self,
		header: &B::Header,
		slot_number: u64,
		epoch_data: &Self::EpochData,
	) -> Option<Self::Claim>;

	/// Return the pre digest data to include in a block authored with the given claim.
	fn pre_digest_data(&self, slot_number: u64, claim: &Self::Claim) -> Vec<sr_primitives::DigestItem<B::Hash>>;

	/// Returns a function which produces a `BlockImportParams`.
	fn import_block(&self) -> Box<dyn Fn(
		B::Header,
		&B::Hash,
		Vec<B::Extrinsic>,
		Self::Claim,
	) -> consensus_common::BlockImportParams<B> + Send>;

	/// Whether to force authoring if offline.
	fn force_authoring(&self) -> bool;

	/// Returns a handle to a `SyncOracle`.
	fn sync_oracle(&mut self) -> &mut Self::SyncOracle;

	/// Returns a `Proposer` to author on top of the given block.
	fn proposer(&mut self, block: &B::Header) -> Result<Self::Proposer, consensus_common::Error>;

	/// Implements the `on_slot` functionality from `SlotWorker`.
	fn on_slot(&mut self, chain_head: B::Header, slot_info: SlotInfo)
		-> Pin<Box<dyn Future<Output = Result<(), consensus_common::Error>> + Send>> where
		Self: Send + Sync,
		<Self::Proposer as Proposer<B>>::Create: Unpin + Send + 'static,
	{
		let (timestamp, slot_number, slot_duration) =
			(slot_info.timestamp, slot_info.number, slot_info.duration);

		let epoch_data = match self.epoch_data(&chain_head.hash()) {
			Ok(epoch_data) => epoch_data,
			Err(err) => {
				warn!("Unable to fetch epoch data at block {:?}: {:?}", chain_head.hash(), err);

				telemetry!(
					CONSENSUS_WARN; "slots.unable_fetching_authorities";
					"slot" => ?chain_head.hash(),
					"err" => ?err,
				);

				return Box::pin(future::ready(Ok(())));
			}
		};

		let authorities_len = self.authorities_len(&epoch_data);

		if !self.force_authoring() && self.sync_oracle().is_offline() && authorities_len > 1 {
			debug!(target: self.logging_target(), "Skipping proposal slot. Waiting for the network.");
			telemetry!(
				CONSENSUS_DEBUG;
				"slots.skipping_proposal_slot";
				"authorities_len" => authorities_len,
			);

			return Box::pin(future::ready(Ok(())));
		}

		let claim = match self.claim_slot(&chain_head, slot_number, &epoch_data) {
			None => return Box::pin(future::ready(Ok(()))),
			Some(claim) => claim,
		};

		debug!(
			target: self.logging_target(), "Starting authorship at slot {}; timestamp = {}",
			slot_number,
			timestamp,
		);

		telemetry!(CONSENSUS_DEBUG; "slots.starting_authorship";
			"slot_num" => slot_number,
			"timestamp" => timestamp,
		);

		let mut proposer = match self.proposer(&chain_head) {
			Ok(proposer) => proposer,
			Err(err) => {
				warn!("Unable to author block in slot {:?}: {:?}", slot_number, err);

				telemetry!(CONSENSUS_WARN; "slots.unable_authoring_block";
					"slot" => slot_number, "err" => ?err
				);

				return Box::pin(future::ready(Ok(())));
			},
		};

		let remaining_duration = slot_info.remaining_duration();
		let logs = self.pre_digest_data(slot_number, &claim);

		// deadline our production to approx. the end of the slot
		let proposal_work = futures::future::select(
			proposer.propose(
				slot_info.inherent_data,
				sr_primitives::generic::Digest {
					logs,
				},
				remaining_duration,
			).map_err(|e| consensus_common::Error::ClientImport(format!("{:?}", e)).into()),
			Delay::new(remaining_duration)
				.map_err(|err| consensus_common::Error::FaultyTimer(err).into())
		).map(|v| match v {
			futures::future::Either::Left((b, _)) => b.map(|b| (b, claim)),
			futures::future::Either::Right((Ok(_), _)) =>
				Err(consensus_common::Error::ClientImport("Timeout in the Slots proposer".into())),
			futures::future::Either::Right((Err(err), _)) => Err(err),
		});

		let import_block = self.import_block();
		let block_import = self.block_import();
		let logging_target = self.logging_target();

		Box::pin(proposal_work.map_ok(move |(block, claim)| {
			// minor hack since we don't have access to the timestamp
			// that is actually set by the proposer.
			let slot_after_building = SignedDuration::default().slot_now(slot_duration);
			if slot_after_building != slot_number {
				info!("Discarding proposal for slot {}; block production took too long", slot_number);
				telemetry!(CONSENSUS_INFO; "slots.discarding_proposal_took_too_long";
					"slot" => slot_number,
				);

				return;
			}

			let (header, body) = block.deconstruct();
			let header_num = header.number().clone();
			let header_hash = header.hash();
			let parent_hash = header.parent_hash().clone();

			let import_block = import_block(
				header,
				&header_hash,
				body,
				claim,
			);

			info!("Pre-sealed block for proposal at {}. Hash now {:?}, previously {:?}.",
					header_num,
					import_block.post_header().hash(),
					header_hash,
			);

			telemetry!(CONSENSUS_INFO; "slots.pre_sealed_block";
				"header_num" => ?header_num,
				"hash_now" => ?import_block.post_header().hash(),
				"hash_previously" => ?header_hash,
			);

			if let Err(err) = block_import.lock().import_block(import_block, Default::default()) {
				warn!(target: logging_target,
					"Error with block built on {:?}: {:?}",
					parent_hash,
					err,
				);

				telemetry!(CONSENSUS_WARN; "slots.err_with_block_built_on";
					"hash" => ?parent_hash, "err" => ?err,
				);
			}
		}))
	}
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
				.map_err(|_| {
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
