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

//! Slots functionality for Substrate.
//!
//! Some consensus algorithms have a concept of *slots*, which are intervals in
//! time during which certain events can and/or must occur.  This crate
//! provides generic functionality for slots.

#![forbid(unsafe_code, missing_docs)]

mod slots;
mod aux_schema;

pub use slots::SlotInfo;
use slots::Slots;
pub use aux_schema::{check_equivocation, MAX_SLOT_CAPACITY, PRUNING_BOUND};

use codec::{Decode, Encode};
use sp_consensus::{BlockImport, Proposer, SyncOracle, SelectChain, CanAuthorWith, SlotData, RecordProof};
use futures::{prelude::*, future::{self, Either}};
use futures_timer::Delay;
use sp_inherents::{InherentData, InherentDataProviders};
use log::{debug, error, info, warn};
use sp_runtime::generic::BlockId;
use sp_runtime::traits::{Block as BlockT, Header, HashFor, NumberFor};
use sp_api::{ProvideRuntimeApi, ApiRef};
use std::{fmt::Debug, ops::Deref, pin::Pin, sync::Arc, time::{Instant, Duration}};
use sc_telemetry::{telemetry, CONSENSUS_DEBUG, CONSENSUS_WARN, CONSENSUS_INFO};
use parking_lot::Mutex;

/// The changes that need to applied to the storage to create the state for a block.
///
/// See [`sp_state_machine::StorageChanges`] for more information.
pub type StorageChanges<Transaction, Block> =
	sp_state_machine::StorageChanges<Transaction, HashFor<Block>, NumberFor<Block>>;

/// The result of [`SlotWorker::on_slot`].
#[derive(Debug, Clone)]
pub struct SlotResult<Block: BlockT> {
	/// The block that was built.
	pub block: Block,
	/// The optional storage proof that was calculated while building the block.
	///
	/// This needs to be enabled for the proposer to get this storage proof.
	pub storage_proof: Option<sp_trie::StorageProof>,
}

/// A worker that should be invoked at every new slot.
///
/// The implementation should not make any assumptions of the slot being bound to the time or
/// similar. The only valid assumption is that the slot number is always increasing.
pub trait SlotWorker<B: BlockT> {
	/// The type of the future that will be returned when a new slot is triggered.
	type OnSlot: Future<Output = Option<SlotResult<B>>>;

	/// Called when a new slot is triggered.
	///
	/// Returns a future that resolves to a [`SlotResult`] iff a block was successfully built in
	/// the slot. Otherwise `None` is returned.
	fn on_slot(&mut self, chain_head: B::Header, slot_info: SlotInfo) -> Self::OnSlot;
}

/// A skeleton implementation for `SlotWorker` which tries to claim a slot at
/// its beginning and tries to produce a block if successfully claimed, timing
/// out if block production takes too long.
pub trait SimpleSlotWorker<B: BlockT> {
	/// A handle to a `BlockImport`.
	type BlockImport: BlockImport<B, Transaction = <Self::Proposer as Proposer<B>>::Transaction>
		+ Send + 'static;

	/// A handle to a `SyncOracle`.
	type SyncOracle: SyncOracle;

	/// The type of future resolving to the proposer.
	type CreateProposer: Future<Output = Result<Self::Proposer, sp_consensus::Error>>
		+ Send + Unpin + 'static;

	/// The type of proposer to use to build blocks.
	type Proposer: Proposer<B>;

	/// Data associated with a slot claim.
	type Claim: Send + 'static;

	/// Epoch data necessary for authoring.
	type EpochData: Send + 'static;

	/// The logging target to use when logging messages.
	fn logging_target(&self) -> &'static str;

	/// A handle to a `BlockImport`.
	fn block_import(&self) -> Arc<Mutex<Self::BlockImport>>;

	/// Returns the epoch data necessary for authoring. For time-dependent epochs,
	/// use the provided slot number as a canonical source of time.
	fn epoch_data(
		&self,
		header: &B::Header,
		slot_number: u64,
	) -> Result<Self::EpochData, sp_consensus::Error>;

	/// Returns the number of authorities given the epoch data.
	/// None indicate that the authorities information is incomplete.
	fn authorities_len(&self, epoch_data: &Self::EpochData) -> Option<usize>;

	/// Tries to claim the given slot, returning an object with claim data if successful.
	fn claim_slot(
		&self,
		header: &B::Header,
		slot_number: u64,
		epoch_data: &Self::EpochData,
	) -> Option<Self::Claim>;

	/// Notifies the given slot. Similar to `claim_slot`, but will be called no matter whether we
	/// need to author blocks or not.
	fn notify_slot(
		&self,
		_header: &B::Header,
		_slot_number: u64,
		_epoch_data: &Self::EpochData,
	) {}

	/// Return the pre digest data to include in a block authored with the given claim.
	fn pre_digest_data(
		&self,
		slot_number: u64,
		claim: &Self::Claim,
	) -> Vec<sp_runtime::DigestItem<B::Hash>>;

	/// Returns a function which produces a `BlockImportParams`.
	fn block_import_params(&self) -> Box<
		dyn Fn(
			B::Header,
			&B::Hash,
			Vec<B::Extrinsic>,
			StorageChanges<<Self::BlockImport as BlockImport<B>>::Transaction, B>,
			Self::Claim,
			Self::EpochData,
		) -> Result<
				sp_consensus::BlockImportParams<B, <Self::BlockImport as BlockImport<B>>::Transaction>,
				sp_consensus::Error
			> + Send + 'static
	>;

	/// Whether to force authoring if offline.
	fn force_authoring(&self) -> bool;

	/// Returns a handle to a `SyncOracle`.
	fn sync_oracle(&mut self) -> &mut Self::SyncOracle;

	/// Returns a `Proposer` to author on top of the given block.
	fn proposer(&mut self, block: &B::Header) -> Self::CreateProposer;

	/// Remaining duration of the slot.
	fn slot_remaining_duration(&self, slot_info: &SlotInfo) -> Duration {
		let now = Instant::now();
		if now < slot_info.ends_at {
			slot_info.ends_at.duration_since(now)
		} else {
			Duration::from_millis(0)
		}
	}

	/// Remaining duration for proposing. None means unlimited.
	fn proposing_remaining_duration(
		&self,
		_head: &B::Header,
		slot_info: &SlotInfo,
	) -> Option<Duration> {
		Some(self.slot_remaining_duration(slot_info))
	}

	/// Implements [`SlotWorker::on_slot`].
	fn on_slot(
		&mut self,
		chain_head: B::Header,
		slot_info: SlotInfo,
	) -> Pin<Box<dyn Future<Output = Option<SlotResult<B>>> + Send>>
	where
		<Self::Proposer as Proposer<B>>::Proposal: Unpin + Send + 'static,
	{
		let (timestamp, slot_number) = (slot_info.timestamp, slot_info.number);

		let slot_remaining_duration = self.slot_remaining_duration(&slot_info);
		let proposing_remaining_duration = self.proposing_remaining_duration(&chain_head, &slot_info);

		let proposing_remaining = match proposing_remaining_duration {
			Some(r) if r.as_secs() == 0 && r.as_nanos() == 0 => {
				debug!(
					target: self.logging_target(),
					"Skipping proposal slot {} since there's no time left to propose",
					slot_number,
				);

				return Box::pin(future::ready(None));
			},
			Some(r) => Box::new(Delay::new(r)) as Box<dyn Future<Output = ()> + Unpin + Send>,
			None => Box::new(future::pending()) as Box<_>,
		};

		let epoch_data = match self.epoch_data(&chain_head, slot_number) {
			Ok(epoch_data) => epoch_data,
			Err(err) => {
				warn!("Unable to fetch epoch data at block {:?}: {:?}", chain_head.hash(), err);

				telemetry!(
					CONSENSUS_WARN; "slots.unable_fetching_authorities";
					"slot" => ?chain_head.hash(),
					"err" => ?err,
				);

				return Box::pin(future::ready(None));
			}
		};

		self.notify_slot(&chain_head, slot_number, &epoch_data);

		let authorities_len = self.authorities_len(&epoch_data);

		if !self.force_authoring() &&
			self.sync_oracle().is_offline() &&
			authorities_len.map(|a| a > 1).unwrap_or(false)
		{
			debug!(target: self.logging_target(), "Skipping proposal slot. Waiting for the network.");
			telemetry!(
				CONSENSUS_DEBUG;
				"slots.skipping_proposal_slot";
				"authorities_len" => authorities_len,
			);

			return Box::pin(future::ready(None));
		}

		let claim = match self.claim_slot(&chain_head, slot_number, &epoch_data) {
			None => return Box::pin(future::ready(None)),
			Some(claim) => claim,
		};

		debug!(
			target: self.logging_target(),
			"Starting authorship at slot {}; timestamp = {}",
			slot_number,
			timestamp,
		);

		telemetry!(CONSENSUS_DEBUG; "slots.starting_authorship";
			"slot_num" => slot_number,
			"timestamp" => timestamp,
		);

		let awaiting_proposer = self.proposer(&chain_head).map_err(move |err| {
			warn!("Unable to author block in slot {:?}: {:?}", slot_number, err);

			telemetry!(CONSENSUS_WARN; "slots.unable_authoring_block";
				"slot" => slot_number, "err" => ?err
			);

			err
		});

		let logs = self.pre_digest_data(slot_number, &claim);

		// deadline our production to approx. the end of the slot
		let proposing = awaiting_proposer.and_then(move |proposer| proposer.propose(
			slot_info.inherent_data,
			sp_runtime::generic::Digest {
				logs,
			},
			slot_remaining_duration,
			RecordProof::No,
		).map_err(|e| sp_consensus::Error::ClientImport(format!("{:?}", e))));

		let proposal_work =
			futures::future::select(proposing, proposing_remaining).map(move |v| match v {
				Either::Left((b, _)) => b.map(|b| (b, claim)),
				Either::Right(_) => {
					info!("⌛️ Discarding proposal for slot {}; block production took too long", slot_number);
					// If the node was compiled with debug, tell the user to use release optimizations.
					#[cfg(build_type="debug")]
					info!("👉 Recompile your node in `--release` mode to mitigate this problem.");
					telemetry!(CONSENSUS_INFO; "slots.discarding_proposal_took_too_long";
						"slot" => slot_number,
					);

					Err(sp_consensus::Error::ClientImport("Timeout in the Slots proposer".into()))
				},
			});

		let block_import_params_maker = self.block_import_params();
		let block_import = self.block_import();
		let logging_target = self.logging_target();

		proposal_work.and_then(move |(proposal, claim)| async move {
			let (block, storage_proof) = (proposal.block, proposal.proof);
			let (header, body) = block.clone().deconstruct();
			let header_num = *header.number();
			let header_hash = header.hash();
			let parent_hash = *header.parent_hash();

			let block_import_params = block_import_params_maker(
				header,
				&header_hash,
				body,
				proposal.storage_changes,
				claim,
				epoch_data,
			)?;

			info!(
				"🔖 Pre-sealed block for proposal at {}. Hash now {:?}, previously {:?}.",
				header_num,
				block_import_params.post_hash(),
				header_hash,
			);

			telemetry!(CONSENSUS_INFO; "slots.pre_sealed_block";
				"header_num" => ?header_num,
				"hash_now" => ?block_import_params.post_hash(),
				"hash_previously" => ?header_hash,
			);

			if let Err(err) = block_import.lock().import_block(block_import_params, Default::default()) {
				warn!(
					target: logging_target,
					"Error with block built on {:?}: {:?}",
					parent_hash,
					err,
				);

				telemetry!(
					CONSENSUS_WARN; "slots.err_with_block_built_on";
					"hash" => ?parent_hash,
					"err" => ?err,
				);
			}

			Ok(SlotResult { block, storage_proof })
		}).then(|r| async move {
			r.map_err(|e| warn!(target: "slots", "Encountered consensus error: {:?}", e)).ok()
		}).boxed()
	}
}

impl<B: BlockT, T: SimpleSlotWorker<B>> SlotWorker<B> for T {
	type OnSlot = Pin<Box<dyn Future<Output = Option<SlotResult<B>>> + Send>>;

	fn on_slot(&mut self, chain_head: B::Header, slot_info: SlotInfo) -> Self::OnSlot {
		SimpleSlotWorker::on_slot(self, chain_head, slot_info)
	}
}

/// Slot compatible inherent data.
pub trait SlotCompatible {
	/// Extract timestamp and slot from inherent data.
	fn extract_timestamp_and_slot(
		&self,
		inherent: &InherentData,
	) -> Result<(u64, u64, std::time::Duration), sp_consensus::Error>;
}

/// Start a new slot worker.
///
/// Every time a new slot is triggered, `worker.on_slot` is called and the future it returns is
/// polled until completion, unless we are major syncing.
pub fn start_slot_worker<B, C, W, T, SO, SC, CAW>(
	slot_duration: SlotDuration<T>,
	client: C,
	mut worker: W,
	mut sync_oracle: SO,
	inherent_data_providers: InherentDataProviders,
	timestamp_extractor: SC,
	can_author_with: CAW,
) -> impl Future<Output = ()>
where
	B: BlockT,
	C: SelectChain<B>,
	W: SlotWorker<B>,
	W::OnSlot: Unpin,
	SO: SyncOracle + Send,
	SC: SlotCompatible + Unpin,
	T: SlotData + Clone,
	CAW: CanAuthorWith<B> + Send,
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

			if let Err(err) = can_author_with.can_author_with(&BlockId::Hash(chain_head.hash())) {
				warn!(
					target: "slots",
					"Unable to author block in slot {},. `can_author_with` returned: {} \
					Probably a node update is required!",
					slot_num,
					err,
				);
				Either::Right(future::ready(Ok(())))
			} else {
				Either::Left(
					worker.on_slot(chain_head, slot_info).then(|_| future::ready(Ok(())))
				)
			}
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

/// A slot duration. Create with `get_or_compute`.
// The internal member should stay private here to maintain invariants of
// `get_or_compute`.
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
	pub fn get_or_compute<B: BlockT, C, CB>(client: &C, cb: CB) -> sp_blockchain::Result<Self> where
		C: sc_client_api::backend::AuxStore,
		C: ProvideRuntimeApi<B>,
		CB: FnOnce(ApiRef<C::Api>, &BlockId<B>) -> sp_blockchain::Result<T>,
		T: SlotData + Encode + Decode + Debug,
	{
		let slot_duration = match client.get_aux(T::SLOT_KEY)? {
			Some(v) => <T as codec::Decode>::decode(&mut &v[..])
				.map(SlotDuration)
				.map_err(|_| {
					sp_blockchain::Error::Backend({
						error!(target: "slots", "slot duration kept in invalid format");
						"slot duration kept in invalid format".to_string()
					})
				}),
			None => {
				use sp_runtime::traits::Zero;
				let genesis_slot_duration =
					cb(client.runtime_api(), &BlockId::number(Zero::zero()))?;

				info!(
					"⏱  Loaded block-time = {:?} milliseconds from genesis on first-launch",
					genesis_slot_duration.slot_duration()
				);

				genesis_slot_duration
					.using_encoded(|s| client.insert_aux(&[(T::SLOT_KEY, &s[..])], &[]))?;

				Ok(SlotDuration(genesis_slot_duration))
			}
		}?;

		if slot_duration.slot_duration() == 0 {
			return Err(sp_blockchain::Error::Msg(
				"Invalid value for slot_duration: the value must be greater than 0.".into(),
			))
		}

		Ok(slot_duration)
	}

	/// Returns slot data value.
	pub fn get(&self) -> T {
		self.0.clone()
	}
}

/// Calculate a slot duration lenience based on the number of missed slots from current
/// to parent. If the number of skipped slots is greated than 0 this method will apply
/// an exponential backoff of at most `2^7 * slot_duration`, if no slots were skipped
/// this method will return `None.`
pub fn slot_lenience_exponential(parent_slot: u64, slot_info: &SlotInfo) -> Option<Duration> {
	// never give more than 2^this times the lenience.
	const BACKOFF_CAP: u64 = 7;

	// how many slots it takes before we double the lenience.
	const BACKOFF_STEP: u64 = 2;

	// we allow a lenience of the number of slots since the head of the
	// chain was produced, minus 1 (since there is always a difference of at least 1)
	//
	// exponential back-off.
	// in normal cases we only attempt to issue blocks up to the end of the slot.
	// when the chain has been stalled for a few slots, we give more lenience.
	let skipped_slots = slot_info.number.saturating_sub(parent_slot + 1);

	if skipped_slots == 0 {
		None
	} else {
		let slot_lenience = skipped_slots / BACKOFF_STEP;
		let slot_lenience = std::cmp::min(slot_lenience, BACKOFF_CAP);
		let slot_lenience = 1 << slot_lenience;
		Some(Duration::from_millis(slot_lenience * slot_info.duration))
	}
}

/// Calculate a slot duration lenience based on the number of missed slots from current
/// to parent. If the number of skipped slots is greated than 0 this method will apply
/// a linear backoff of at most `20 * slot_duration`, if no slots were skipped
/// this method will return `None.`
pub fn slot_lenience_linear(parent_slot: u64, slot_info: &SlotInfo) -> Option<Duration> {
	// never give more than 20 times more lenience.
	const BACKOFF_CAP: u64 = 20;

	// we allow a lenience of the number of slots since the head of the
	// chain was produced, minus 1 (since there is always a difference of at least 1)
	//
	// linear back-off.
	// in normal cases we only attempt to issue blocks up to the end of the slot.
	// when the chain has been stalled for a few slots, we give more lenience.
	let skipped_slots = slot_info.number.saturating_sub(parent_slot + 1);

	if skipped_slots == 0 {
		None
	} else {
		let slot_lenience = std::cmp::min(skipped_slots, BACKOFF_CAP);
		Some(Duration::from_millis(slot_lenience * slot_info.duration))
	}
}

#[cfg(test)]
mod test {
	use std::time::{Duration, Instant};

	const SLOT_DURATION: Duration = Duration::from_millis(6000);

	fn slot(n: u64) -> super::slots::SlotInfo {
		super::slots::SlotInfo {
			number: n,
			duration: SLOT_DURATION.as_millis() as u64,
			timestamp: Default::default(),
			inherent_data: Default::default(),
			ends_at: Instant::now(),
		}
	}

	#[test]
	fn linear_slot_lenience() {
		// if no slots are skipped there should be no lenience
		assert_eq!(super::slot_lenience_linear(1, &slot(2)), None);

		// otherwise the lenience is incremented linearly with
		// the number of skipped slots.
		for n in 3..=22 {
			assert_eq!(
				super::slot_lenience_linear(1, &slot(n)),
				Some(SLOT_DURATION * (n - 2) as u32),
			);
		}

		// but we cap it to a maximum of 20 slots
		assert_eq!(
			super::slot_lenience_linear(1, &slot(23)),
			Some(SLOT_DURATION * 20),
		);
	}

	#[test]
	fn exponential_slot_lenience() {
		// if no slots are skipped there should be no lenience
		assert_eq!(super::slot_lenience_exponential(1, &slot(2)), None);

		// otherwise the lenience is incremented exponentially every two slots
		for n in 3..=17 {
			assert_eq!(
				super::slot_lenience_exponential(1, &slot(n)),
				Some(SLOT_DURATION * 2u32.pow((n / 2 - 1) as u32)),
			);
		}

		// but we cap it to a maximum of 14 slots
		assert_eq!(
			super::slot_lenience_exponential(1, &slot(18)),
			Some(SLOT_DURATION * 2u32.pow(7)),
		);

		assert_eq!(
			super::slot_lenience_exponential(1, &slot(19)),
			Some(SLOT_DURATION * 2u32.pow(7)),
		);
	}
}
