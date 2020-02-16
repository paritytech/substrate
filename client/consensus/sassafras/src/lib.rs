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

//! # Sassafras

pub use sp_consensus_sassafras::{
	SassafrasApi, ConsensusLog, SASSAFRAS_ENGINE_ID, SlotNumber, SassafrasConfiguration,
	AuthorityId, AuthorityPair, AuthoritySignature,
	SassafrasAuthorityWeight, VRF_OUTPUT_LENGTH,
	digests::{PreDigest, CompatibleDigestItem, NextEpochDescriptor},
};
pub use sp_consensus::SyncOracle;
use std::{
	collections::HashMap, sync::Arc, u64, pin::Pin, time::{Instant, Duration},
	any::Any, borrow::Cow
};
use sp_consensus_sassafras;
use sp_consensus::{ImportResult, CanAuthorWith};
use sp_consensus::import_queue::{
	BoxJustificationImport, BoxFinalityProofImport,
};
use sp_runtime::{
	generic::{BlockId, OpaqueDigestItemId}, Justification,
	traits::{Block as BlockT, Header, DigestItemFor, Zero},
};
use sp_api::{ProvideRuntimeApi, NumberFor};
use sc_keystore::KeyStorePtr;
use parking_lot::Mutex;
use sp_core::Pair;
use sp_inherents::{InherentDataProviders, InherentData};
use sc_telemetry::{telemetry, CONSENSUS_TRACE, CONSENSUS_DEBUG};
use sp_consensus::{
	self, BlockImport, Environment, Proposer, BlockCheckParams,
	ForkChoiceStrategy, BlockImportParams, BlockOrigin, Error as ConsensusError,
	SelectChain, SlotData,
};
use sp_consensus_sassafras::inherents::SassafrasInherentData;
use sp_timestamp::{TimestampInherentData, InherentType as TimestampInherent};
use sp_consensus::import_queue::{Verifier, BasicQueue, CacheKeyId};
use sc_client_api::{
	backend::{AuxStore, Backend},
	call_executor::CallExecutor,
	BlockchainEvents, ProvideUncles,
};
use sc_client::Client;

use sp_block_builder::BlockBuilder as BlockBuilderApi;

use futures::prelude::*;
use log::{warn, debug, info, trace};
use sc_consensus_slots::{
	SlotWorker, SlotInfo, SlotCompatible, StorageChanges, CheckedHeader, check_equivocation,
};
use sc_consensus_epochs::{
	descendent_query, SharedEpochChanges, EpochChangesFor, Epoch as EpochT, ViableEpochDescriptor,
};
use sp_blockchain::{
	Result as ClientResult, Error as ClientError,
	HeaderBackend, ProvideCache, HeaderMetadata
};
use schnorrkel::SignatureError;
use codec::{Encode, Decode};
use sp_api::ApiExt;

mod aux_schema;
mod verification;
mod authorship;
#[cfg(test)]
mod tests;

/// Validator set of a particular epoch, can be either publishing or validating.
#[derive(Debug, Clone, Encode, Decode)]
pub struct ValidatorSet {
	/// Proofs of all VRFs collected.
	pub proofs: Vec<VRFProof>,
	/// The authorities and their weights.
	pub authorities: Vec<(AuthorityId, SassafrasAuthorityWeight)>,
	/// Randomness for this epoch.
	pub randomness: Randomness,
}

/// Epoch data for Sassafras
#[derive(Debug, Clone, Encode, Decode)]
pub struct Epoch {
	/// Start slot of the epoch.
	pub start_slot: SlotNumber,
	/// Duration of this epoch.
	pub duration: SlotNumber,
	/// Epoch index.
	pub epoch_index: u64,

	/// Publishing validator set. The set will start validating block in the next epoch.
	pub publishing: ValidatorSet,
	/// Validating validator set. The set validates block in the current epoch.
	pub validating: ValidatorSet,
}

impl EpochT for Epoch {
	type SlotNumber = SlotNumber;
	type NextEpochDescriptor = NextEpochDescriptor;

	fn increment(&self, descriptor: NextEpochDescriptor) -> Epoch {
		Epoch {
			epoch_index: self.epoch_index + 1,
			start_slot: self.start_slot + self.duration,
			duration: self.duration,

			validating: self.publishing.clone(),
			publishing: ValidatorSet {
				proofs: Vec::new(),
				authorities: descriptor.authorities,
				randomness: descriptor.randomness,
			},
		}
	}

	fn start_slot(&self) -> SlotNumber {
		self.start_slot
	}

	fn end_slot(&self) -> SlotNumber {
		self.start_slot + self.duration
	}
}

#[derive(derive_more::Display, Debug)]
enum Error<B: BlockT> {
	#[display(fmt = "Multiple Sassafras pre-runtime digests, rejecting!")]
	MultiplePreRuntimeDigests,
	#[display(fmt = "No Sassafras pre-runtime digest found")]
	NoPreRuntimeDigest,
	#[display(fmt = "Multiple Sassafras epoch change digests, rejecting!")]
	MultipleEpochChangeDigests,
	#[display(fmt = "Could not extract timestamp and slot: {:?}", _0)]
	Extraction(sp_consensus::Error),
	#[display(fmt = "Could not fetch epoch at {:?}", _0)]
	FetchEpoch(B::Hash),
	#[display(fmt = "Header {:?} rejected: too far in the future", _0)]
	TooFarInFuture(B::Hash),
	#[display(fmt = "Parent ({}) of {} unavailable. Cannot import", _0, _1)]
	ParentUnavailable(B::Hash, B::Hash),
	#[display(fmt = "Slot number must increase: parent slot: {}, this slot: {}", _0, _1)]
	SlotNumberMustIncrease(u64, u64),
	#[display(fmt = "Header {:?} has a bad seal", _0)]
	HeaderBadSeal(B::Hash),
	#[display(fmt = "Header {:?} is unsealed", _0)]
	HeaderUnsealed(B::Hash),
	#[display(fmt = "Slot author not found")]
	SlotAuthorNotFound,
	#[display(fmt = "Secondary slot assignments are disabled for the current epoch.")]
	SecondarySlotAssignmentsDisabled,
	#[display(fmt = "Bad signature on {:?}", _0)]
	BadSignature(B::Hash),
	#[display(fmt = "Invalid author: Expected secondary author: {:?}, got: {:?}.", _0, _1)]
	InvalidAuthor(AuthorityId, AuthorityId),
	#[display(fmt = "No secondary author expected.")]
	NoSecondaryAuthorExpected,
	#[display(fmt = "VRF verification of block by author {:?} failed: threshold {} exceeded", _0, _1)]
	VRFVerificationOfBlockFailed(AuthorityId, u128),
	#[display(fmt = "VRF verification failed: {:?}", _0)]
	VRFVerificationFailed(SignatureError),
	#[display(fmt = "Could not fetch parent header: {:?}", _0)]
	FetchParentHeader(sp_blockchain::Error),
	#[display(fmt = "Expected epoch change to happen at {:?}, s{}", _0, _1)]
	ExpectedEpochChange(B::Hash, u64),
	#[display(fmt = "Unexpected epoch change")]
	UnexpectedEpochChange,
	#[display(fmt = "Parent block of {} has no associated weight", _0)]
	ParentBlockNoAssociatedWeight(B::Hash),
	#[display(fmt = "Checking inherents failed: {}", _0)]
	CheckInherents(String),
	Client(sp_blockchain::Error),
	Runtime(sp_inherents::Error),
	ForkTree(Box<fork_tree::Error<sp_blockchain::Error>>),
}

impl<B: BlockT> std::convert::From<Error<B>> for String {
	fn from(error: Error<B>) -> String {
		error.to_string()
	}
}

/// Intermediate value passed to block importer.
pub struct SassafrasIntermediate<B: BlockT> {
	/// The epoch descriptor.
	pub epoch_descriptor: ViableEpochDescriptor<B::Hash, NumberFor<B>, Epoch>,
}

/// Intermediate key for Sassafras engine.
pub static INTERMEDIATE_KEY: &[u8] = b"sassafras1";

/// A slot duration. Create with `get_or_compute`.
#[derive(Clone)]
pub struct Config(sc_consensus_slots::SlotDuration<SassafrasConfiguration>);

impl Config {
	/// Either fetch the slot duration from disk or compute it from the genesis
	/// state.
	pub fn get_or_compute<B: BlockT, C>(client: &C) -> ClientResult<Self> where
		C: AuxStore + ProvideRuntimeApi<B>, C::Api: SassafrasApi<B, Error = sp_blockchain::Error>,
	{
		trace!(target: "sassafras", "Getting slot duration");
		match sc_consensus_slots::SlotDuration::get_or_compute(client, |a, b| a.configuration(b)).map(Self) {
			Ok(s) => Ok(s),
			Err(s) => {
				warn!(target: "sassafras", "Failed to get slot duration");
				Err(s)
			}
		}
	}

	/// Create the genesis epoch (epoch #0). This is defined to start at the slot of
	/// the first block, so that has to be provided.
	pub fn genesis_epoch(&self, slot_number: SlotNumber) -> Epoch {
		Epoch {
			epoch_index: 0,
			start_slot: slot_number,
			duration: self.epoch_length,
			authorities: self.genesis_authorities.clone(),
			randomness: self.randomness.clone(),
		}
	}
}

impl std::ops::Deref for Config {
	type Target = SassafrasConfiguration;

	fn deref(&self) -> &SassafrasConfiguration {
		&*self.0
	}
}

/// Parameters for Sassafras.
pub struct SassafrasParams<B: BlockT, C, E, I, SO, SC, CAW> {
	/// The keystore that manages the keys of the node.
	pub keystore: KeyStorePtr,

	/// The client to use
	pub client: Arc<C>,

	/// The SelectChain Strategy
	pub select_chain: SC,

	/// The environment we are producing blocks for.
	pub env: E,

	/// The underlying block-import object to supply our produced blocks to.
	/// This must be a `SassafrasBlockImport` or a wrapper of it, otherwise
	/// critical consensus logic will be omitted.
	pub block_import: I,

	/// A sync oracle
	pub sync_oracle: SO,

	/// Providers for inherent data.
	pub inherent_data_providers: InherentDataProviders,

	/// Force authoring of blocks even if we are offline
	pub force_authoring: bool,

	/// The source of timestamps for relative slots
	pub sassafras_link: SassafrasLink<B>,

	/// Checks if the current native implementation can author with a runtime at a given block.
	pub can_author_with: CAW,
}

/// Start the sassafras worker. The returned future should be run in a tokio runtime.
pub fn start_sassafras<B, C, SC, E, I, SO, CAW, Error>(SassafrasParams {
	keystore,
	client,
	select_chain,
	env,
	block_import,
	sync_oracle,
	inherent_data_providers,
	force_authoring,
	sassafras_link,
	can_author_with,
}: SassafrasParams<B, C, E, I, SO, SC, CAW>) -> Result<
	impl futures::Future<Output=()>,
	sp_consensus::Error,
> where
	B: BlockT,
	C: ProvideRuntimeApi<B> + ProvideCache<B> + ProvideUncles<B> + BlockchainEvents<B>
		+ HeaderBackend<B> + HeaderMetadata<B, Error = ClientError> + Send + Sync + 'static,
	C::Api: SassafrasApi<B>,
	SC: SelectChain<B> + 'static,
	E: Environment<B, Error = Error> + Send + Sync,
	E::Proposer: Proposer<B, Error = Error, Transaction = sp_api::TransactionFor<C, B>>,
	I: BlockImport<B, Error = ConsensusError, Transaction = sp_api::TransactionFor<C, B>> + Send
		+ Sync + 'static,
	Error: std::error::Error + Send + From<ConsensusError> + From<I::Error> + 'static,
	SO: SyncOracle + Send + Sync + Clone,
	CAW: CanAuthorWith<B> + Send,
{
	let config = sassafras_link.config;
	let worker = SassafrasWorker {
		client: client.clone(),
		block_import: Arc::new(Mutex::new(block_import)),
		env,
		sync_oracle: sync_oracle.clone(),
		force_authoring,
		keystore,
		epoch_changes: sassafras_link.epoch_changes.clone(),
		config: config.clone(),
	};

	register_sassafras_inherent_data_provider(&inherent_data_providers, config.slot_duration())?;
	sc_consensus_uncles::register_uncles_inherent_data_provider(
		client.clone(),
		select_chain.clone(),
		&inherent_data_providers,
	)?;

	info!(target: "sassafras", "Starting Sassafras authorship worker");
	Ok(sc_consensus_slots::start_slot_worker(
		config.0,
		select_chain,
		worker,
		sync_oracle,
		inherent_data_providers,
		sassafras_link.time_source,
		can_author_with,
	))
}

struct SassafrasWorker<B: BlockT, C, E, I, SO> {
	client: Arc<C>,
	block_import: Arc<Mutex<I>>,
	env: E,
	sync_oracle: SO,
	force_authoring: bool,
	keystore: KeyStorePtr,
	epoch_changes: SharedEpochChanges<B, Epoch>,
	config: Config,
}

impl<B, C, E, I, Error, SO> sc_consensus_slots::SimpleSlotWorker<B> for SassafrasWorker<B, C, E, I, SO> where
	B: BlockT,
	C: ProvideRuntimeApi<B> +
		ProvideCache<B> +
		HeaderBackend<B> +
		HeaderMetadata<B, Error = ClientError>,
	C::Api: SassafrasApi<B>,
	E: Environment<B, Error = Error>,
	E::Proposer: Proposer<B, Error = Error, Transaction = sp_api::TransactionFor<C, B>>,
	I: BlockImport<B, Transaction = sp_api::TransactionFor<C, B>> + Send + Sync + 'static,
	SO: SyncOracle + Send + Clone,
	Error: std::error::Error + Send + From<ConsensusError> + From<I::Error> + 'static,
{
	type EpochData = ViableEpochDescriptor<B::Hash, NumberFor<B>, Epoch>;
	type Claim = (PreDigest, AuthorityPair);
	type SyncOracle = SO;
	type CreateProposer = Pin<Box<
		dyn Future<Output = Result<E::Proposer, sp_consensus::Error>> + Send + 'static
	>>;
	type Proposer = E::Proposer;
	type BlockImport = I;

	fn logging_target(&self) -> &'static str {
		"sassafras"
	}

	fn block_import(&self) -> Arc<Mutex<Self::BlockImport>> {
		self.block_import.clone()
	}

	fn epoch_data(
		&self,
		parent: &B::Header,
		slot_number: u64,
	) -> Result<Self::EpochData, ConsensusError> {
		self.epoch_changes.lock().epoch_descriptor_for_child_of(
			descendent_query(&*self.client),
			&parent.hash(),
			parent.number().clone(),
			slot_number,
		)
			.map_err(|e| ConsensusError::ChainLookup(format!("{:?}", e)))?
			.ok_or(sp_consensus::Error::InvalidAuthoritiesSet)
	}

	fn authorities_len(&self, epoch_descriptor: &Self::EpochData) -> Option<usize> {
		self.epoch_changes.lock()
			.viable_epoch(&epoch_descriptor, |slot| self.config.genesis_epoch(slot))
			.map(|epoch| epoch.as_ref().authorities.len())
	}

	fn claim_slot(
		&self,
		_parent_header: &B::Header,
		slot_number: SlotNumber,
		epoch_descriptor: &ViableEpochDescriptor<B::Hash, NumberFor<B>, Epoch>,
	) -> Option<Self::Claim> {
		debug!(target: "sassafras", "Attempting to claim slot {}", slot_number);
		let s = authorship::claim_slot(
			slot_number,
			self.epoch_changes.lock().viable_epoch(
				&epoch_descriptor,
				|slot| self.config.genesis_epoch(slot)
			)?.as_ref(),
			&*self.config,
			&self.keystore,
		);

		if let Some(_) = s {
			debug!(target: "sassafras", "Claimed slot {}", slot_number);
		}

		s
	}

	fn pre_digest_data(
		&self,
		_slot_number: u64,
		claim: &Self::Claim,
	) -> Vec<sp_runtime::DigestItem<B::Hash>> {
		vec![
			<DigestItemFor<B> as CompatibleDigestItem>::sassafras_pre_digest(claim.0.clone()),
		]
	}

	fn block_import_params(&self) -> Box<dyn Fn(
		B::Header,
		&B::Hash,
		Vec<B::Extrinsic>,
		StorageChanges<I::Transaction, B>,
		Self::Claim,
		Self::EpochData,
	) -> sp_consensus::BlockImportParams<B, I::Transaction> + Send> {
		Box::new(|header, header_hash, body, storage_changes, (_, pair), epoch_descriptor| {
			// sign the pre-sealed hash of the block and then
			// add it to a digest item.
			let signature = pair.sign(header_hash.as_ref());
			let digest_item = <DigestItemFor<B> as CompatibleDigestItem>::sassafras_seal(signature);

			BlockImportParams {
				origin: BlockOrigin::Own,
				header,
				justification: None,
				post_digests: vec![digest_item],
				body: Some(body),
				storage_changes: Some(storage_changes),
				finalized: false,
				auxiliary: Vec::new(), // block-weight is written in block import.
				intermediates: {
					let mut intermediates = HashMap::new();
					intermediates.insert(
						Cow::from(INTERMEDIATE_KEY),
						Box::new(SassafrasIntermediate::<B> { epoch_descriptor }) as Box<dyn Any>,
					);
					intermediates
				},
				fork_choice: None,
				allow_missing_state: false,
				import_existing: false,
			}
		})
	}

	fn force_authoring(&self) -> bool {
		self.force_authoring
	}

	fn sync_oracle(&mut self) -> &mut Self::SyncOracle {
		&mut self.sync_oracle
	}

	fn proposer(&mut self, block: &B::Header) -> Self::CreateProposer {
		Box::pin(self.env.init(block).map_err(|e| {
			sp_consensus::Error::ClientImport(format!("{:?}", e))
		}))
	}

	fn proposing_remaining_duration(
		&self,
		head: &B::Header,
		slot_info: &SlotInfo
	) -> Option<std::time::Duration> {
		// never give more than 2^this times the lenience.
		const BACKOFF_CAP: u64 = 8;

		// how many slots it takes before we double the lenience.
		const BACKOFF_STEP: u64 = 2;

		let slot_remaining = self.slot_remaining_duration(slot_info);
		let parent_slot = match find_pre_digest::<B>(head) {
			Err(_) => return Some(slot_remaining),
			Ok(d) => d.slot_number(),
		};

		// we allow a lenience of the number of slots since the head of the
		// chain was produced, minus 1 (since there is always a difference of at least 1)
		//
		// exponential back-off.
		// in normal cases we only attempt to issue blocks up to the end of the slot.
		// when the chain has been stalled for a few slots, we give more lenience.
		let slot_lenience = slot_info.number.saturating_sub(parent_slot + 1);

		let slot_lenience = std::cmp::min(slot_lenience, BACKOFF_CAP);
		let slot_duration = slot_info.duration << (slot_lenience / BACKOFF_STEP);

		if slot_lenience >= 1 {
			debug!(target: "sassafras", "No block for {} slots. Applying 2^({}/{}) lenience",
				slot_lenience, slot_lenience, BACKOFF_STEP);
		}

		let slot_lenience = Duration::from_secs(slot_duration);
		Some(slot_lenience + slot_remaining)
	}
}

impl<B, C, E, I, Error, SO> SlotWorker<B> for SassafrasWorker<B, C, E, I, SO> where
	B: BlockT,
	C: ProvideRuntimeApi<B> +
		ProvideCache<B> +
		HeaderBackend<B> +
		HeaderMetadata<B, Error = ClientError> + Send + Sync,
	C::Api: SassafrasApi<B>,
	E: Environment<B, Error = Error> + Send + Sync,
	E::Proposer: Proposer<B, Error = Error, Transaction = sp_api::TransactionFor<C, B>>,
	I: BlockImport<B, Transaction = sp_api::TransactionFor<C, B>> + Send + Sync + 'static,
	SO: SyncOracle + Send + Sync + Clone,
	Error: std::error::Error + Send + From<sp_consensus::Error> + From<I::Error> + 'static,
{
	type OnSlot = Pin<Box<dyn Future<Output = Result<(), sp_consensus::Error>> + Send>>;

	fn on_slot(&mut self, chain_head: B::Header, slot_info: SlotInfo) -> Self::OnSlot {
		<Self as sc_consensus_slots::SimpleSlotWorker<B>>::on_slot(self, chain_head, slot_info)
	}
}

/// Extract the Sassafras pre digest from the given header. Pre-runtime digests are
/// mandatory, the function will return `Err` if none is found.
fn find_pre_digest<B: BlockT>(header: &B::Header) -> Result<PreDigest, Error<B>>
{
	// genesis block doesn't contain a pre digest so let's generate a
	// dummy one to not break any invariants in the rest of the code
	if header.number().is_zero() {
		return Ok(PreDigest::Secondary {
			slot_number: 0,
			authority_index: 0,
		});
	}

	let mut pre_digest: Option<_> = None;
	for log in header.digest().logs() {
		trace!(target: "sassafras", "Checking log {:?}, looking for pre runtime digest", log);
		match (log.as_sassafras_pre_digest(), pre_digest.is_some()) {
			(Some(_), true) => return Err(Error::MultiplePreRuntimeDigests),
			(None, _) => trace!(target: "sassafras", "Ignoring digest not meant for us"),
			(s, false) => pre_digest = s,
		}
	}
	pre_digest.ok_or_else(|| Error::NoPreRuntimeDigest)
}

/// Extract the Sassafras epoch change digest from the given header, if it exists.
fn find_next_epoch_digest<B: BlockT>(header: &B::Header)
	-> Result<Option<NextEpochDescriptor>, Error<B>>
	where DigestItemFor<B>: CompatibleDigestItem,
{
	let mut epoch_digest: Option<_> = None;
	for log in header.digest().logs() {
		trace!(target: "sassafras", "Checking log {:?}, looking for epoch change digest.", log);
		let log = log.try_to::<ConsensusLog>(OpaqueDigestItemId::Consensus(&SASSAFRAS_ENGINE_ID));
		match (log, epoch_digest.is_some()) {
			(Some(ConsensusLog::NextEpochData(_)), true) => return Err(Error::MultipleEpochChangeDigests),
			(Some(ConsensusLog::NextEpochData(epoch)), false) => epoch_digest = Some(epoch),
			_ => trace!(target: "sassafras", "Ignoring digest not meant for us"),
		}
	}

	Ok(epoch_digest)
}


#[derive(Default, Clone)]
struct TimeSource(Arc<Mutex<(Option<Duration>, Vec<(Instant, u64)>)>>);

impl SlotCompatible for TimeSource {
	fn extract_timestamp_and_slot(
		&self,
		data: &InherentData,
	) -> Result<(TimestampInherent, u64, std::time::Duration), sp_consensus::Error> {
		trace!(target: "sassafras", "extract timestamp");
		data.timestamp_inherent_data()
			.and_then(|t| data.sassafras_inherent_data().map(|a| (t, a)))
			.map_err(Into::into)
			.map_err(sp_consensus::Error::InherentData)
			.map(|(x, y)| (x, y, self.0.lock().0.take().unwrap_or_default()))
	}
}

/// State that must be shared between the import queue and the authoring logic.
#[derive(Clone)]
pub struct SassafrasLink<Block: BlockT> {
	time_source: TimeSource,
	epoch_changes: SharedEpochChanges<Block, Epoch>,
	config: Config,
}

impl<Block: BlockT> SassafrasLink<Block> {
	/// Get the epoch changes of this link.
	pub fn epoch_changes(&self) -> &SharedEpochChanges<Block, Epoch> {
		&self.epoch_changes
	}

	/// Get the config of this link.
	pub fn config(&self) -> &Config {
		&self.config
	}
}

/// A verifier for Sassafras blocks.
pub struct SassafrasVerifier<B, E, Block: BlockT, RA, PRA> {
	client: Arc<Client<B, E, Block, RA>>,
	api: Arc<PRA>,
	inherent_data_providers: sp_inherents::InherentDataProviders,
	config: Config,
	epoch_changes: SharedEpochChanges<Block, Epoch>,
	time_source: TimeSource,
}

impl<B, E, Block: BlockT, RA, PRA> SassafrasVerifier<B, E, Block, RA, PRA> {
	fn check_inherents(
		&self,
		block: Block,
		block_id: BlockId<Block>,
		inherent_data: InherentData,
	) -> Result<(), Error<Block>>
		where
			PRA: ProvideRuntimeApi<Block>,
			PRA::Api: BlockBuilderApi<Block, Error = sp_blockchain::Error>
	{
		let inherent_res = self.api.runtime_api().check_inherents(
			&block_id,
			block,
			inherent_data,
		).map_err(Error::Client)?;

		if !inherent_res.ok() {
			inherent_res
				.into_errors()
				.try_for_each(|(i, e)| {
					Err(Error::CheckInherents(self.inherent_data_providers.error_to_string(&i, &e)))
				})
		} else {
			Ok(())
		}
	}
}

#[allow(dead_code)]
fn median_algorithm(
	median_required_blocks: u64,
	slot_duration: u64,
	slot_number: u64,
	slot_now: u64,
	time_source: &mut (Option<Duration>, Vec<(Instant, u64)>),
) {
	let num_timestamps = time_source.1.len();
	if num_timestamps as u64 >= median_required_blocks && median_required_blocks > 0 {
		let mut new_list: Vec<_> = time_source.1.iter().map(|&(t, sl)| {
			let offset: u128 = u128::from(slot_duration)
				.checked_mul(1_000_000u128) // self.config.slot_duration returns milliseconds
				.and_then(|x| {
					x.checked_mul(u128::from(slot_number).saturating_sub(u128::from(sl)))
				})
				.expect("we cannot have timespans long enough for this to overflow; qed");

			const NANOS_PER_SEC: u32 = 1_000_000_000;
			let nanos = (offset % u128::from(NANOS_PER_SEC)) as u32;
			let secs = (offset / u128::from(NANOS_PER_SEC)) as u64;

			t + Duration::new(secs, nanos)
		}).collect();

		// Use a partial sort to move the median timestamp to the middle of the list
		pdqselect::select(&mut new_list, num_timestamps / 2);

		let &median = new_list
			.get(num_timestamps / 2)
			.expect("we have at least one timestamp, so this is a valid index; qed");

		let now = Instant::now();
		if now >= median {
			time_source.0.replace(now - median);
		}

		time_source.1.clear();
	} else {
		time_source.1.push((Instant::now(), slot_now))
	}
}

impl<B, E, Block, RA, PRA> Verifier<Block> for SassafrasVerifier<B, E, Block, RA, PRA> where
	Block: BlockT,
	B: Backend<Block> + 'static,
	E: CallExecutor<Block> + 'static + Clone + Send + Sync,
	RA: Send + Sync,
	PRA: ProvideRuntimeApi<Block> + Send + Sync + AuxStore + ProvideCache<Block>,
	PRA::Api: BlockBuilderApi<Block, Error = sp_blockchain::Error>
		+ SassafrasApi<Block, Error = sp_blockchain::Error>,
{
	fn verify(
		&mut self,
		origin: BlockOrigin,
		header: Block::Header,
		justification: Option<Justification>,
		mut body: Option<Vec<Block::Extrinsic>>,
	) -> Result<(BlockImportParams<Block, ()>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
		trace!(
			target: "sassafras",
			"Verifying origin: {:?} header: {:?} justification: {:?} body: {:?}",
			origin,
			header,
			justification,
			body,
		);

		debug!(target: "sassafras", "We have {:?} logs in this header", header.digest().logs().len());
		let mut inherent_data = self
			.inherent_data_providers
			.create_inherent_data()
			.map_err(Error::<Block>::Runtime)?;

		let (_, slot_now, _) = self.time_source.extract_timestamp_and_slot(&inherent_data)
			.map_err(Error::<Block>::Extraction)?;

		let hash = header.hash();
		let parent_hash = *header.parent_hash();

		let parent_header_metadata = self.client.header_metadata(parent_hash)
			.map_err(Error::<Block>::FetchParentHeader)?;

		let pre_digest = find_pre_digest::<Block>(&header)?;
		let epoch_changes = self.epoch_changes.lock();
		let epoch_descriptor = epoch_changes.epoch_descriptor_for_child_of(
			descendent_query(&*self.client),
			&parent_hash,
			parent_header_metadata.number,
			pre_digest.slot_number(),
		)
			.map_err(|e| Error::<Block>::ForkTree(Box::new(e)))?
			.ok_or_else(|| Error::<Block>::FetchEpoch(parent_hash))?;
		let viable_epoch = epoch_changes.viable_epoch(
			&epoch_descriptor,
			|slot| self.config.genesis_epoch(slot)
		).ok_or_else(|| Error::<Block>::FetchEpoch(parent_hash))?;

		// We add one to the current slot to allow for some small drift.
		// FIXME #1019 in the future, alter this queue to allow deferring of headers
		let v_params = verification::VerificationParams {
			header: header.clone(),
			pre_digest: Some(pre_digest.clone()),
			slot_now: slot_now + 1,
			epoch: viable_epoch.as_ref(),
			config: &self.config,
		};

		match verification::check_header::<Block>(v_params)? {
			CheckedHeader::Checked(pre_header, verified_info) => {
				let sassafras_pre_digest = verified_info.pre_digest.as_sassafras_pre_digest()
					.expect("check_header always returns a pre-digest digest item; qed");

				let slot_number = sassafras_pre_digest.slot_number();

				let author = verified_info.author;

				// the header is valid but let's check if there was something else already
				// proposed at the same slot by the given author
				if let Some(equivocation_proof) = check_equivocation(
					&*self.api,
					slot_now,
					sassafras_pre_digest.slot_number(),
					&header,
					&author,
				).map_err(|e| e.to_string())? {
					info!(
						"Slot author {:?} is equivocating at slot {} with headers {:?} and {:?}",
						author,
						sassafras_pre_digest.slot_number(),
						equivocation_proof.fst_header().hash(),
						equivocation_proof.snd_header().hash(),
					);
				}

				// if the body is passed through, we need to use the runtime
				// to check that the internally-set timestamp in the inherents
				// actually matches the slot set in the seal.
				if let Some(inner_body) = body.take() {
					inherent_data.sassafras_replace_inherent_data(slot_number);
					let block = Block::new(pre_header.clone(), inner_body);

					self.check_inherents(
						block.clone(),
						BlockId::Hash(parent_hash),
						inherent_data,
					)?;

					let (_, inner_body) = block.deconstruct();
					body = Some(inner_body);
				}

				trace!(target: "sassafras", "Checked {:?}; importing.", pre_header);
				telemetry!(
					CONSENSUS_TRACE;
					"sassafras.checked_and_importing";
					"pre_header" => ?pre_header);

				let mut intermediates = HashMap::new();
				intermediates.insert(
					Cow::from(INTERMEDIATE_KEY),
					Box::new(SassafrasIntermediate::<Block> {
						epoch_descriptor,
					}) as Box<dyn Any>,
				);

				let block_import_params = BlockImportParams {
					origin,
					header: pre_header,
					post_digests: vec![verified_info.seal],
					body,
					storage_changes: None,
					finalized: false,
					justification,
					auxiliary: Vec::new(),
					intermediates,
					fork_choice: None,
					allow_missing_state: false,
					import_existing: false,
				};

				Ok((block_import_params, Default::default()))
			}
			CheckedHeader::Deferred(a, b) => {
				debug!(target: "sassafras", "Checking {:?} failed; {:?}, {:?}.", hash, a, b);
				telemetry!(CONSENSUS_DEBUG; "sassafras.header_too_far_in_future";
					"hash" => ?hash, "a" => ?a, "b" => ?b
				);
				Err(Error::<Block>::TooFarInFuture(hash).into())
			}
		}
	}
}

/// The Sassafras import queue type.
pub type SassafrasImportQueue<B, Transaction> = BasicQueue<B, Transaction>;

/// Register the Sassafras inherent data provider, if not registered already.
fn register_sassafras_inherent_data_provider(
	inherent_data_providers: &InherentDataProviders,
	slot_duration: u64,
) -> Result<(), sp_consensus::Error> {
	debug!(target: "sassafras", "Registering");
	if !inherent_data_providers.has_provider(&sp_consensus_sassafras::inherents::INHERENT_IDENTIFIER) {
		inherent_data_providers
			.register_provider(sp_consensus_sassafras::inherents::InherentDataProvider::new(slot_duration))
			.map_err(Into::into)
			.map_err(sp_consensus::Error::InherentData)
	} else {
		Ok(())
	}
}

/// A block-import handler for Sassafras.
///
/// This scans each imported block for epoch change signals. The signals are
/// tracked in a tree (of all forks), and the import logic validates all epoch
/// change transitions, i.e. whether a given epoch change is expected or whether
/// it is missing.
///
/// The epoch change tree should be pruned as blocks are finalized.
pub struct SassafrasBlockImport<B, E, Block: BlockT, I, RA, PRA> {
	inner: I,
	client: Arc<Client<B, E, Block, RA>>,
	api: Arc<PRA>,
	epoch_changes: SharedEpochChanges<Block, Epoch>,
	config: Config,
}

impl<B, E, Block: BlockT, I: Clone, RA, PRA> Clone for SassafrasBlockImport<B, E, Block, I, RA, PRA> {
	fn clone(&self) -> Self {
		SassafrasBlockImport {
			inner: self.inner.clone(),
			client: self.client.clone(),
			api: self.api.clone(),
			epoch_changes: self.epoch_changes.clone(),
			config: self.config.clone(),
		}
	}
}

impl<B, E, Block: BlockT, I, RA, PRA> SassafrasBlockImport<B, E, Block, I, RA, PRA> {
	fn new(
		client: Arc<Client<B, E, Block, RA>>,
		api: Arc<PRA>,
		epoch_changes: SharedEpochChanges<Block, Epoch>,
		block_import: I,
		config: Config,
	) -> Self {
		SassafrasBlockImport {
			client,
			api,
			inner: block_import,
			epoch_changes,
			config,
		}
	}
}

impl<B, E, Block, I, RA, PRA> BlockImport<Block> for SassafrasBlockImport<B, E, Block, I, RA, PRA> where
	Block: BlockT,
	I: BlockImport<Block, Transaction = sp_api::TransactionFor<PRA, Block>> + Send + Sync,
	I::Error: Into<ConsensusError>,
	B: Backend<Block> + 'static,
	E: CallExecutor<Block> + 'static + Clone + Send + Sync,
	Client<B, E, Block, RA>: AuxStore,
	RA: Send + Sync,
	PRA: ProvideRuntimeApi<Block> + ProvideCache<Block>,
	PRA::Api: SassafrasApi<Block> + ApiExt<Block, StateBackend = B::State>,
{
	type Error = ConsensusError;
	type Transaction = sp_api::TransactionFor<PRA, Block>;

	fn import_block(
		&mut self,
		mut block: BlockImportParams<Block, Self::Transaction>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		let hash = block.post_header().hash();
		let number = block.header.number().clone();

		// early exit if block already in chain, otherwise the check for
		// epoch changes will error when trying to re-import an epoch change
		match self.client.status(BlockId::Hash(hash)) {
			Ok(sp_blockchain::BlockStatus::InChain) => return Ok(ImportResult::AlreadyInChain),
			Ok(sp_blockchain::BlockStatus::Unknown) => {},
			Err(e) => return Err(ConsensusError::ClientImport(e.to_string())),
		}

		let pre_digest = find_pre_digest::<Block>(&block.header)
			.expect("valid sassafras headers must contain a predigest; \
					 header has been already verified; qed");
		let slot_number = pre_digest.slot_number();

		let parent_hash = *block.header.parent_hash();
		let parent_header = self.client.header(&BlockId::Hash(parent_hash))
			.map_err(|e| ConsensusError::ChainLookup(e.to_string()))?
			.ok_or_else(|| ConsensusError::ChainLookup(
				Error::<Block>::ParentUnavailable(parent_hash, hash).into()
			))?;

		let parent_slot = find_pre_digest::<Block>(&parent_header)
			.map(|d| d.slot_number())
			.expect("parent is non-genesis; valid Sassafras headers contain a pre-digest; \
					header has already been verified; qed");

		// make sure that slot number is strictly increasing
		if slot_number <= parent_slot {
			return Err(
				ConsensusError::ClientImport(
					Error::<Block>::SlotNumberMustIncrease(parent_slot, slot_number).into()
				)
			);
		}

		let mut epoch_changes = self.epoch_changes.lock();

		// check if there's any epoch change expected to happen at this slot.
		// `epoch` is the epoch to verify the block under, and `first_in_epoch` is true
		// if this is the first block in its chain for that epoch.
		//
		// also provides the total weight of the chain, including the imported block.
		let (epoch_descriptor, first_in_epoch, parent_weight) = {
			let parent_weight = if *parent_header.number() == Zero::zero() {
				0
			} else {
				aux_schema::load_block_weight(&*self.client, parent_hash)
					.map_err(|e| ConsensusError::ClientImport(e.to_string()))?
					.ok_or_else(|| ConsensusError::ClientImport(
						Error::<Block>::ParentBlockNoAssociatedWeight(hash).into()
					))?
			};

			let intermediate = block.take_intermediate::<SassafrasIntermediate<Block>>(
				INTERMEDIATE_KEY
			)?;

			let epoch_descriptor = intermediate.epoch_descriptor;
			let first_in_epoch = parent_slot < epoch_descriptor.start_slot();
			(epoch_descriptor, first_in_epoch, parent_weight)
		};

		let total_weight = parent_weight + pre_digest.added_weight();

		// search for this all the time so we can reject unexpected announcements.
		let next_epoch_digest = find_next_epoch_digest::<Block>(&block.header)
			.map_err(|e| ConsensusError::ClientImport(e.to_string()))?;

		match (first_in_epoch, next_epoch_digest.is_some()) {
			(true, true) => {},
			(false, false) => {},
			(true, false) => {
				return Err(
					ConsensusError::ClientImport(
						Error::<Block>::ExpectedEpochChange(hash, slot_number).into(),
					)
				);
			},
			(false, true) => {
				return Err(ConsensusError::ClientImport(Error::<Block>::UnexpectedEpochChange.into()));
			},
		}

		// if there's a pending epoch we'll save the previous epoch changes here
		// this way we can revert it if there's any error
		let mut old_epoch_changes = None;

		let info = self.client.chain_info();

		if let Some(next_epoch_descriptor) = next_epoch_digest {
			old_epoch_changes = Some(epoch_changes.clone());

			let viable_epoch = epoch_changes.viable_epoch(
				&epoch_descriptor,
				|slot| self.config.genesis_epoch(slot),
			).ok_or_else(|| {
				ConsensusError::ClientImport(Error::<Block>::FetchEpoch(parent_hash).into())
			})?;

			info!(target: "sassafras",
				  "New epoch {} launching at block {} (block slot {} >= start slot {}).",
				  viable_epoch.as_ref().epoch_index,
				  hash,
				  slot_number,
				  viable_epoch.as_ref().start_slot);

			let next_epoch = viable_epoch.increment(next_epoch_descriptor);

			info!(target: "sassafras",
				  "Next epoch starts at slot {}",
				  next_epoch.as_ref().start_slot);

			// prune the tree of epochs not part of the finalized chain or
			// that are not live anymore, and then track the given epoch change
			// in the tree.
			// NOTE: it is important that these operations are done in this
			// order, otherwise if pruning after import the `is_descendent_of`
			// used by pruning may not know about the block that is being
			// imported.
			let prune_and_import = || {
				prune_finalized(
					&self.client,
					&mut epoch_changes,
				)?;

				epoch_changes.import(
					descendent_query(&*self.client),
					hash,
					number,
					*block.header.parent_hash(),
					next_epoch,
				).map_err(|e| ConsensusError::ClientImport(format!("{:?}", e)))?;

				Ok(())
			};

			if let Err(e) = prune_and_import() {
				debug!(target: "sassafras", "Failed to launch next epoch: {:?}", e);
				*epoch_changes = old_epoch_changes.expect("set `Some` above and not taken; qed");
				return Err(e);
			}

			crate::aux_schema::write_epoch_changes::<Block, _, _>(
				&*epoch_changes,
				|insert| block.auxiliary.extend(
					insert.iter().map(|(k, v)| (k.to_vec(), Some(v.to_vec())))
				)
			);
		}

		aux_schema::write_block_weight(
			hash,
			&total_weight,
			|values| block.auxiliary.extend(
				values.iter().map(|(k, v)| (k.to_vec(), Some(v.to_vec())))
			),
		);

		// The fork choice rule is that we pick the heaviest chain (i.e.
		// more primary blocks), if there's a tie we go with the longest
		// chain.
		block.fork_choice = {
			let (last_best, last_best_number) = (info.best_hash, info.best_number);

			let last_best_weight = if &last_best == block.header.parent_hash() {
				// the parent=genesis case is already covered for loading parent weight,
				// so we don't need to cover again here.
				parent_weight
			} else {
				aux_schema::load_block_weight(&*self.client, last_best)
					.map_err(|e| ConsensusError::ChainLookup(format!("{:?}", e)))?
					.ok_or_else(
						|| ConsensusError::ChainLookup(format!("No block weight for parent header."))
					)?
			};

			Some(ForkChoiceStrategy::Custom(if total_weight > last_best_weight {
				true
			} else if total_weight == last_best_weight {
				number > last_best_number
			} else {
				false
			}))
		};

		let import_result = self.inner.import_block(block, new_cache);

		// revert to the original epoch changes in case there's an error
		// importing the block
		if let Err(_) = import_result {
			if let Some(old_epoch_changes) = old_epoch_changes {
				*epoch_changes = old_epoch_changes;
			}
		}

		import_result.map_err(Into::into)
	}

	fn check_block(
		&mut self,
		block: BlockCheckParams<Block>,
	) -> Result<ImportResult, Self::Error> {
		self.inner.check_block(block).map_err(Into::into)
	}
}

/// Gets the best finalized block and its slot, and prunes the given epoch tree.
fn prune_finalized<B, E, Block, RA>(
	client: &Client<B, E, Block, RA>,
	epoch_changes: &mut EpochChangesFor<Block, Epoch>,
) -> Result<(), ConsensusError> where
	Block: BlockT,
	E: CallExecutor<Block> + Send + Sync,
	B: Backend<Block>,
	RA: Send + Sync,
{
	let info = client.chain_info();

	let finalized_slot = {
		let finalized_header = client.header(&BlockId::Hash(info.finalized_hash))
			.map_err(|e| ConsensusError::ClientImport(format!("{:?}", e)))?
			.expect("best finalized hash was given by client; \
				 finalized headers must exist in db; qed");

		find_pre_digest::<Block>(&finalized_header)
			.expect("finalized header must be valid; \
					 valid blocks have a pre-digest; qed")
			.slot_number()
	};

	epoch_changes.prune_finalized(
		descendent_query(&*client),
		&info.finalized_hash,
		info.finalized_number,
		finalized_slot,
	).map_err(|e| ConsensusError::ClientImport(format!("{:?}", e)))?;

	Ok(())
}

/// Produce a Sassafras block-import object to be used later on in the construction of
/// an import-queue.
///
/// Also returns a link object used to correctly instantiate the import queue
/// and background worker.
pub fn block_import<B, E, Block: BlockT, I, RA, PRA>(
	config: Config,
	wrapped_block_import: I,
	client: Arc<Client<B, E, Block, RA>>,
	api: Arc<PRA>,
) -> ClientResult<(SassafrasBlockImport<B, E, Block, I, RA, PRA>, SassafrasLink<Block>)> where
	B: Backend<Block>,
	E: CallExecutor<Block> + Send + Sync,
	RA: Send + Sync,
	Client<B, E, Block, RA>: AuxStore,
{
	let epoch_changes = aux_schema::load_epoch_changes::<Block, _>(&*client)?;
	let link = SassafrasLink {
		epoch_changes: epoch_changes.clone(),
		time_source: Default::default(),
		config: config.clone(),
	};

	// NOTE: this isn't entirely necessary, but since we didn't use to prune the
	// epoch tree it is useful as a migration, so that nodes prune long trees on
	// startup rather than waiting until importing the next epoch change block.
	prune_finalized(
		&client,
		&mut epoch_changes.lock(),
	)?;

	let import = SassafrasBlockImport::new(
		client,
		api,
		epoch_changes,
		wrapped_block_import,
		config,
	);

	Ok((import, link))
}

/// Start an import queue for the Sassafras consensus algorithm.
///
/// This method returns the import queue, some data that needs to be passed to the block authoring
/// logic (`SassafrasLink`), and a future that must be run to
/// completion and is responsible for listening to finality notifications and
/// pruning the epoch changes tree.
///
/// The block import object provided must be the `SassafrasBlockImport` or a wrapper
/// of it, otherwise crucial import logic will be omitted.
pub fn import_queue<B, E, Block: BlockT, I, RA, PRA>(
	sassafras_link: SassafrasLink<Block>,
	block_import: I,
	justification_import: Option<BoxJustificationImport<Block>>,
	finality_proof_import: Option<BoxFinalityProofImport<Block>>,
	client: Arc<Client<B, E, Block, RA>>,
	api: Arc<PRA>,
	inherent_data_providers: InherentDataProviders,
) -> ClientResult<SassafrasImportQueue<Block, sp_api::TransactionFor<PRA, Block>>> where
	B: Backend<Block> + 'static,
	I: BlockImport<Block, Error = ConsensusError, Transaction = sp_api::TransactionFor<PRA, Block>>
		+ Send + Sync + 'static,
	E: CallExecutor<Block> + Clone + Send + Sync + 'static,
	RA: Send + Sync + 'static,
	PRA: ProvideRuntimeApi<Block> + ProvideCache<Block> + Send + Sync + AuxStore + 'static,
	PRA::Api: BlockBuilderApi<Block> + SassafrasApi<Block> + ApiExt<Block, Error = sp_blockchain::Error>,
{
	register_sassafras_inherent_data_provider(&inherent_data_providers, sassafras_link.config.slot_duration)?;

	let verifier = SassafrasVerifier {
		client: client.clone(),
		api,
		inherent_data_providers,
		config: sassafras_link.config,
		epoch_changes: sassafras_link.epoch_changes,
		time_source: sassafras_link.time_source,
	};

	Ok(BasicQueue::new(
		verifier,
		Box::new(block_import),
		justification_import,
		finality_proof_import,
	))
}
