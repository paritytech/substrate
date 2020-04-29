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

//! # BABE (Blind Assignment for Blockchain Extension)
//!
//! BABE is a slot-based block production mechanism which uses a VRF PRNG to
//! randomly perform the slot allocation. On every slot, all the authorities
//! generate a new random number with the VRF function and if it is lower than a
//! given threshold (which is proportional to their weight/stake) they have a
//! right to produce a block. The proof of the VRF function execution will be
//! used by other peer to validate the legitimacy of the slot claim.
//!
//! The engine is also responsible for collecting entropy on-chain which will be
//! used to seed the given VRF PRNG. An epoch is a contiguous number of slots
//! under which we will be using the same authority set. During an epoch all VRF
//! outputs produced as a result of block production will be collected on an
//! on-chain randomness pool. Epoch changes are announced one epoch in advance,
//! i.e. when ending epoch N, we announce the parameters (randomness,
//! authorities, etc.) for epoch N+2.
//!
//! Since the slot assignment is randomized, it is possible that a slot is
//! assigned to multiple validators in which case we will have a temporary fork,
//! or that a slot is assigned to no validator in which case no block is
//! produced. Which means that block times are not deterministic.
//!
//! The protocol has a parameter `c` [0, 1] for which `1 - c` is the probability
//! of a slot being empty. The choice of this parameter affects the security of
//! the protocol relating to maximum tolerable network delays.
//!
//! In addition to the VRF-based slot assignment described above, which we will
//! call primary slots, the engine also supports a deterministic secondary slot
//! assignment. Primary slots take precedence over secondary slots, when
//! authoring the node starts by trying to claim a primary slot and falls back
//! to a secondary slot claim attempt. The secondary slot assignment is done
//! by picking the authority at index:
//!
//! `blake2_256(epoch_randomness ++ slot_number) % authorities_len`.
//!
//! The secondary slots supports either a `SecondaryPlain` or `SecondaryVRF`
//! variant. Comparing with `SecondaryPlain` variant, the `SecondaryVRF` variant
//! generates an additional VRF output. The output is not included in beacon
//! randomness, but can be consumed by parachains.
//!
//! The fork choice rule is weight-based, where weight equals the number of
//! primary blocks in the chain. We will pick the heaviest chain (more primary
//! blocks) and will go with the longest one in case of a tie.
//!
//! An in-depth description and analysis of the protocol can be found here:
//! <https://research.web3.foundation/en/latest/polkadot/BABE/Babe.html>

#![forbid(unsafe_code)]
#![warn(missing_docs)]
pub use sp_consensus_babe::{
	BabeApi, ConsensusLog, BABE_ENGINE_ID, SlotNumber,
	BabeEpochConfiguration, BabeGenesisConfiguration,
	AuthorityId, AuthorityPair, AuthoritySignature,
	BabeAuthorityWeight, VRF_OUTPUT_LENGTH,
	digests::{
		CompatibleDigestItem, NextEpochDescriptor, NextConfigDescriptor, PreDigest,
		PrimaryPreDigest, SecondaryPlainPreDigest,
	},
};
pub use sp_consensus::SyncOracle;
use std::{
	collections::HashMap, sync::Arc, u64, pin::Pin, time::{Instant, Duration},
	any::Any, borrow::Cow
};
use sp_consensus_babe;
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
use sp_consensus_babe::inherents::BabeInherentData;
use sp_timestamp::{TimestampInherentData, InherentType as TimestampInherent};
use sp_consensus::import_queue::{Verifier, BasicQueue, CacheKeyId};
use sc_client_api::{
	backend::AuxStore,
	BlockchainEvents, ProvideUncles,
};
use sp_block_builder::BlockBuilder as BlockBuilderApi;

use futures::prelude::*;
use log::{debug, info, log, trace, warn};
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
mod migration;
pub mod authorship;
#[cfg(test)]
mod tests;

/// BABE epoch information
#[derive(Decode, Encode, PartialEq, Eq, Clone, Debug)]
pub struct Epoch {
	/// The epoch index.
	pub epoch_index: u64,
	/// The starting slot of the epoch.
	pub start_slot: SlotNumber,
	/// The duration of this epoch.
	pub duration: SlotNumber,
	/// The authorities and their weights.
	pub authorities: Vec<(AuthorityId, BabeAuthorityWeight)>,
	/// Randomness for this epoch.
	pub randomness: [u8; VRF_OUTPUT_LENGTH],
	/// Configuration of the epoch.
	pub config: BabeEpochConfiguration,
}

impl EpochT for Epoch {
	type NextEpochDescriptor = (NextEpochDescriptor, BabeEpochConfiguration);
	type SlotNumber = SlotNumber;

	fn increment(
		&self,
		(descriptor, config): (NextEpochDescriptor, BabeEpochConfiguration)
	) -> Epoch {
		Epoch {
			epoch_index: self.epoch_index + 1,
			start_slot: self.start_slot + self.duration,
			duration: self.duration,
			authorities: descriptor.authorities,
			randomness: descriptor.randomness,
			config,
		}
	}

	fn start_slot(&self) -> SlotNumber {
		self.start_slot
	}

	fn end_slot(&self) -> SlotNumber {
		self.start_slot + self.duration
	}
}

impl Epoch {
	/// Create the genesis epoch (epoch #0). This is defined to start at the slot of
	/// the first block, so that has to be provided.
	pub fn genesis(
		genesis_config: &BabeGenesisConfiguration,
		slot_number: SlotNumber
	) -> Epoch {
		Epoch {
			epoch_index: 0,
			start_slot: slot_number,
			duration: genesis_config.epoch_length,
			authorities: genesis_config.genesis_authorities.clone(),
			randomness: genesis_config.randomness.clone(),
			config: BabeEpochConfiguration {
				c: genesis_config.c,
				allowed_slots: genesis_config.allowed_slots,
			},
		}
	}
}

#[derive(derive_more::Display, Debug)]
enum Error<B: BlockT> {
	#[display(fmt = "Multiple BABE pre-runtime digests, rejecting!")]
	MultiplePreRuntimeDigests,
	#[display(fmt = "No BABE pre-runtime digest found")]
	NoPreRuntimeDigest,
	#[display(fmt = "Multiple BABE epoch change digests, rejecting!")]
	MultipleEpochChangeDigests,
	#[display(fmt = "Multiple BABE config change digests, rejecting!")]
	MultipleConfigChangeDigests,
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
	#[display(fmt = "Unexpected config change")]
	UnexpectedConfigChange,
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

fn babe_err<B: BlockT>(error: Error<B>) -> Error<B> {
	debug!(target: "babe", "{}", error);
	error
}

/// Intermediate value passed to block importer.
pub struct BabeIntermediate<B: BlockT> {
	/// The epoch descriptor.
	pub epoch_descriptor: ViableEpochDescriptor<B::Hash, NumberFor<B>, Epoch>,
}

/// Intermediate key for Babe engine.
pub static INTERMEDIATE_KEY: &[u8] = b"babe1";

/// A slot duration. Create with `get_or_compute`.
// FIXME: Once Rust has higher-kinded types, the duplication between this
// and `super::babe::Config` can be eliminated.
// https://github.com/paritytech/substrate/issues/2434
#[derive(Clone)]
pub struct Config(sc_consensus_slots::SlotDuration<BabeGenesisConfiguration>);

impl Config {
	/// Either fetch the slot duration from disk or compute it from the genesis
	/// state.
	pub fn get_or_compute<B: BlockT, C>(client: &C) -> ClientResult<Self> where
		C: AuxStore + ProvideRuntimeApi<B>, C::Api: BabeApi<B, Error = sp_blockchain::Error>,
	{
		trace!(target: "babe", "Getting slot duration");
		match sc_consensus_slots::SlotDuration::get_or_compute(client, |a, b| {
			let has_api_v1 = a.has_api_with::<dyn BabeApi<B, Error = sp_blockchain::Error>, _>(
				&b, |v| v == 1,
			)?;
			let has_api_v2 = a.has_api_with::<dyn BabeApi<B, Error = sp_blockchain::Error>, _>(
				&b, |v| v == 2,
			)?;

			if has_api_v1 {
				#[allow(deprecated)] {
					Ok(a.configuration_before_version_2(b)?.into())
				}
			} else if has_api_v2 {
				a.configuration(b)
			} else {
				Err(sp_blockchain::Error::VersionInvalid(
					"Unsupported or invalid BabeApi version".to_string()
				))
			}
		}).map(Self) {
			Ok(s) => Ok(s),
			Err(s) => {
				warn!(target: "babe", "Failed to get slot duration");
				Err(s)
			}
		}
	}
}

impl std::ops::Deref for Config {
	type Target = BabeGenesisConfiguration;

	fn deref(&self) -> &BabeGenesisConfiguration {
		&*self.0
	}
}

/// Parameters for BABE.
pub struct BabeParams<B: BlockT, C, E, I, SO, SC, CAW> {
	/// The keystore that manages the keys of the node.
	pub keystore: KeyStorePtr,

	/// The client to use
	pub client: Arc<C>,

	/// The SelectChain Strategy
	pub select_chain: SC,

	/// The environment we are producing blocks for.
	pub env: E,

	/// The underlying block-import object to supply our produced blocks to.
	/// This must be a `BabeBlockImport` or a wrapper of it, otherwise
	/// critical consensus logic will be omitted.
	pub block_import: I,

	/// A sync oracle
	pub sync_oracle: SO,

	/// Providers for inherent data.
	pub inherent_data_providers: InherentDataProviders,

	/// Force authoring of blocks even if we are offline
	pub force_authoring: bool,

	/// The source of timestamps for relative slots
	pub babe_link: BabeLink<B>,

	/// Checks if the current native implementation can author with a runtime at a given block.
	pub can_author_with: CAW,
}

/// Start the babe worker.
pub fn start_babe<B, C, SC, E, I, SO, CAW, Error>(BabeParams {
	keystore,
	client,
	select_chain,
	env,
	block_import,
	sync_oracle,
	inherent_data_providers,
	force_authoring,
	babe_link,
	can_author_with,
}: BabeParams<B, C, E, I, SO, SC, CAW>) -> Result<
	impl futures::Future<Output=()>,
	sp_consensus::Error,
> where
	B: BlockT,
	C: ProvideRuntimeApi<B> + ProvideCache<B> + ProvideUncles<B> + BlockchainEvents<B>
		+ HeaderBackend<B> + HeaderMetadata<B, Error = ClientError> + Send + Sync + 'static,
	C::Api: BabeApi<B>,
	SC: SelectChain<B> + 'static,
	E: Environment<B, Error = Error> + Send + Sync,
	E::Proposer: Proposer<B, Error = Error, Transaction = sp_api::TransactionFor<C, B>>,
	I: BlockImport<B, Error = ConsensusError, Transaction = sp_api::TransactionFor<C, B>> + Send
		+ Sync + 'static,
	Error: std::error::Error + Send + From<ConsensusError> + From<I::Error> + 'static,
	SO: SyncOracle + Send + Sync + Clone,
	CAW: CanAuthorWith<B> + Send,
{
	let config = babe_link.config;
	let worker = BabeWorker {
		client: client.clone(),
		block_import: Arc::new(Mutex::new(block_import)),
		env,
		sync_oracle: sync_oracle.clone(),
		force_authoring,
		keystore,
		epoch_changes: babe_link.epoch_changes.clone(),
		config: config.clone(),
	};

	register_babe_inherent_data_provider(&inherent_data_providers, config.slot_duration())?;
	sc_consensus_uncles::register_uncles_inherent_data_provider(
		client.clone(),
		select_chain.clone(),
		&inherent_data_providers,
	)?;

	info!(target: "babe", "👶 Starting BABE Authorship worker");
	Ok(sc_consensus_slots::start_slot_worker(
		config.0,
		select_chain,
		worker,
		sync_oracle,
		inherent_data_providers,
		babe_link.time_source,
		can_author_with,
	))
}

struct BabeWorker<B: BlockT, C, E, I, SO> {
	client: Arc<C>,
	block_import: Arc<Mutex<I>>,
	env: E,
	sync_oracle: SO,
	force_authoring: bool,
	keystore: KeyStorePtr,
	epoch_changes: SharedEpochChanges<B, Epoch>,
	config: Config,
}

impl<B, C, E, I, Error, SO> sc_consensus_slots::SimpleSlotWorker<B> for BabeWorker<B, C, E, I, SO> where
	B: BlockT,
	C: ProvideRuntimeApi<B> +
		ProvideCache<B> +
		HeaderBackend<B> +
		HeaderMetadata<B, Error = ClientError>,
	C::Api: BabeApi<B>,
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
		"babe"
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
			.viable_epoch(&epoch_descriptor, |slot| Epoch::genesis(&self.config, slot))
			.map(|epoch| epoch.as_ref().authorities.len())
	}

	fn claim_slot(
		&self,
		_parent_header: &B::Header,
		slot_number: SlotNumber,
		epoch_descriptor: &ViableEpochDescriptor<B::Hash, NumberFor<B>, Epoch>,
	) -> Option<Self::Claim> {
		debug!(target: "babe", "Attempting to claim slot {}", slot_number);
		let s = authorship::claim_slot(
			slot_number,
			self.epoch_changes.lock().viable_epoch(
				&epoch_descriptor,
				|slot| Epoch::genesis(&self.config, slot)
			)?.as_ref(),
			&self.keystore,
		);

		if let Some(_) = s {
			debug!(target: "babe", "Claimed slot {}", slot_number);
		}

		s
	}

	fn pre_digest_data(
		&self,
		_slot_number: u64,
		claim: &Self::Claim,
	) -> Vec<sp_runtime::DigestItem<B::Hash>> {
		vec![
			<DigestItemFor<B> as CompatibleDigestItem>::babe_pre_digest(claim.0.clone()),
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
			let digest_item = <DigestItemFor<B> as CompatibleDigestItem>::babe_seal(signature);

			let mut import_block = BlockImportParams::new(BlockOrigin::Own, header);
			import_block.post_digests.push(digest_item);
			import_block.body = Some(body);
			import_block.storage_changes = Some(storage_changes);
			import_block.intermediates.insert(
				Cow::from(INTERMEDIATE_KEY),
				Box::new(BabeIntermediate::<B> { epoch_descriptor }) as Box<dyn Any>,
			);

			import_block
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
		slot_info: &SlotInfo,
	) -> Option<std::time::Duration> {
		let slot_remaining = self.slot_remaining_duration(slot_info);

		let parent_slot = match find_pre_digest::<B>(head) {
			Err(_) => return Some(slot_remaining),
			Ok(d) => d.slot_number(),
		};

		if let Some(slot_lenience) =
			sc_consensus_slots::slot_lenience_exponential(parent_slot, slot_info)
		{
			debug!(target: "babe",
				"No block for {} slots. Applying exponential lenience of {}s",
				slot_info.number.saturating_sub(parent_slot + 1),
				slot_lenience.as_secs(),
			);

			Some(slot_remaining + slot_lenience)
		} else {
			Some(slot_remaining)
		}
	}
}

impl<B, C, E, I, Error, SO> SlotWorker<B> for BabeWorker<B, C, E, I, SO> where
	B: BlockT,
	C: ProvideRuntimeApi<B> +
		ProvideCache<B> +
		HeaderBackend<B> +
		HeaderMetadata<B, Error = ClientError> + Send + Sync,
	C::Api: BabeApi<B>,
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

/// Extract the BABE pre digest from the given header. Pre-runtime digests are
/// mandatory, the function will return `Err` if none is found.
fn find_pre_digest<B: BlockT>(header: &B::Header) -> Result<PreDigest, Error<B>>
{
	// genesis block doesn't contain a pre digest so let's generate a
	// dummy one to not break any invariants in the rest of the code
	if header.number().is_zero() {
		return Ok(PreDigest::SecondaryPlain(SecondaryPlainPreDigest {
			slot_number: 0,
			authority_index: 0,
		}));
	}

	let mut pre_digest: Option<_> = None;
	for log in header.digest().logs() {
		trace!(target: "babe", "Checking log {:?}, looking for pre runtime digest", log);
		match (log.as_babe_pre_digest(), pre_digest.is_some()) {
			(Some(_), true) => return Err(babe_err(Error::MultiplePreRuntimeDigests)),
			(None, _) => trace!(target: "babe", "Ignoring digest not meant for us"),
			(s, false) => pre_digest = s,
		}
	}
	pre_digest.ok_or_else(|| babe_err(Error::NoPreRuntimeDigest))
}

/// Extract the BABE epoch change digest from the given header, if it exists.
fn find_next_epoch_digest<B: BlockT>(header: &B::Header)
	-> Result<Option<NextEpochDescriptor>, Error<B>>
	where DigestItemFor<B>: CompatibleDigestItem,
{
	let mut epoch_digest: Option<_> = None;
	for log in header.digest().logs() {
		trace!(target: "babe", "Checking log {:?}, looking for epoch change digest.", log);
		let log = log.try_to::<ConsensusLog>(OpaqueDigestItemId::Consensus(&BABE_ENGINE_ID));
		match (log, epoch_digest.is_some()) {
			(Some(ConsensusLog::NextEpochData(_)), true) => return Err(babe_err(Error::MultipleEpochChangeDigests)),
			(Some(ConsensusLog::NextEpochData(epoch)), false) => epoch_digest = Some(epoch),
			_ => trace!(target: "babe", "Ignoring digest not meant for us"),
		}
	}

	Ok(epoch_digest)
}

/// Extract the BABE config change digest from the given header, if it exists.
fn find_next_config_digest<B: BlockT>(header: &B::Header)
	-> Result<Option<NextConfigDescriptor>, Error<B>>
	where DigestItemFor<B>: CompatibleDigestItem,
{
	let mut config_digest: Option<_> = None;
	for log in header.digest().logs() {
		trace!(target: "babe", "Checking log {:?}, looking for epoch change digest.", log);
		let log = log.try_to::<ConsensusLog>(OpaqueDigestItemId::Consensus(&BABE_ENGINE_ID));
		match (log, config_digest.is_some()) {
			(Some(ConsensusLog::NextConfigData(_)), true) => return Err(babe_err(Error::MultipleConfigChangeDigests)),
			(Some(ConsensusLog::NextConfigData(config)), false) => config_digest = Some(config),
			_ => trace!(target: "babe", "Ignoring digest not meant for us"),
		}
	}

	Ok(config_digest)
}

#[derive(Default, Clone)]
struct TimeSource(Arc<Mutex<(Option<Duration>, Vec<(Instant, u64)>)>>);

impl SlotCompatible for TimeSource {
	fn extract_timestamp_and_slot(
		&self,
		data: &InherentData,
	) -> Result<(TimestampInherent, u64, std::time::Duration), sp_consensus::Error> {
		trace!(target: "babe", "extract timestamp");
		data.timestamp_inherent_data()
			.and_then(|t| data.babe_inherent_data().map(|a| (t, a)))
			.map_err(Into::into)
			.map_err(sp_consensus::Error::InherentData)
			.map(|(x, y)| (x, y, self.0.lock().0.take().unwrap_or_default()))
	}
}

/// State that must be shared between the import queue and the authoring logic.
#[derive(Clone)]
pub struct BabeLink<Block: BlockT> {
	time_source: TimeSource,
	epoch_changes: SharedEpochChanges<Block, Epoch>,
	config: Config,
}

impl<Block: BlockT> BabeLink<Block> {
	/// Get the epoch changes of this link.
	pub fn epoch_changes(&self) -> &SharedEpochChanges<Block, Epoch> {
		&self.epoch_changes
	}

	/// Get the config of this link.
	pub fn config(&self) -> &Config {
		&self.config
	}
}

/// A verifier for Babe blocks.
pub struct BabeVerifier<Block: BlockT, Client> {
	client: Arc<Client>,
	inherent_data_providers: sp_inherents::InherentDataProviders,
	config: Config,
	epoch_changes: SharedEpochChanges<Block, Epoch>,
	time_source: TimeSource,
}

impl<Block, Client> BabeVerifier<Block, Client>
	where
		Block: BlockT,
		Client: HeaderBackend<Block> + HeaderMetadata<Block> + ProvideRuntimeApi<Block>,
		Client::Api: BlockBuilderApi<Block, Error = sp_blockchain::Error>,
{
	fn check_inherents(
		&self,
		block: Block,
		block_id: BlockId<Block>,
		inherent_data: InherentData,
	) -> Result<(), Error<Block>>
	{
		let inherent_res = self.client.runtime_api().check_inherents(
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

impl<Block, Client> Verifier<Block> for BabeVerifier<Block, Client> where
	Block: BlockT,
	Client: HeaderMetadata<Block, Error = sp_blockchain::Error> + HeaderBackend<Block> + ProvideRuntimeApi<Block>
	+ Send + Sync + AuxStore + ProvideCache<Block>,
	Client::Api: BlockBuilderApi<Block, Error = sp_blockchain::Error> + BabeApi<Block, Error = sp_blockchain::Error>,
{
	fn verify(
		&mut self,
		origin: BlockOrigin,
		header: Block::Header,
		justification: Option<Justification>,
		mut body: Option<Vec<Block::Extrinsic>>,
	) -> Result<(BlockImportParams<Block, ()>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
		trace!(
			target: "babe",
			"Verifying origin: {:?} header: {:?} justification: {:?} body: {:?}",
			origin,
			header,
			justification,
			body,
		);

		debug!(target: "babe", "We have {:?} logs in this header", header.digest().logs().len());
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
			|slot| Epoch::genesis(&self.config, slot)
		).ok_or_else(|| Error::<Block>::FetchEpoch(parent_hash))?;

		// We add one to the current slot to allow for some small drift.
		// FIXME #1019 in the future, alter this queue to allow deferring of headers
		let v_params = verification::VerificationParams {
			header: header.clone(),
			pre_digest: Some(pre_digest.clone()),
			slot_now: slot_now + 1,
			epoch: viable_epoch.as_ref(),
		};

		match verification::check_header::<Block>(v_params)? {
			CheckedHeader::Checked(pre_header, verified_info) => {
				let babe_pre_digest = verified_info.pre_digest.as_babe_pre_digest()
					.expect("check_header always returns a pre-digest digest item; qed");

				let slot_number = babe_pre_digest.slot_number();

				let author = verified_info.author;

				// the header is valid but let's check if there was something else already
				// proposed at the same slot by the given author
				if let Some(equivocation_proof) = check_equivocation(
					&*self.client,
					slot_now,
					babe_pre_digest.slot_number(),
					&header,
					&author,
				).map_err(|e| e.to_string())? {
					info!(
						"Slot author {:?} is equivocating at slot {} with headers {:?} and {:?}",
						author,
						babe_pre_digest.slot_number(),
						equivocation_proof.fst_header().hash(),
						equivocation_proof.snd_header().hash(),
					);
				}

				// if the body is passed through, we need to use the runtime
				// to check that the internally-set timestamp in the inherents
				// actually matches the slot set in the seal.
				if let Some(inner_body) = body.take() {
					inherent_data.babe_replace_inherent_data(slot_number);
					let block = Block::new(pre_header.clone(), inner_body);

					self.check_inherents(
						block.clone(),
						BlockId::Hash(parent_hash),
						inherent_data,
					)?;

					let (_, inner_body) = block.deconstruct();
					body = Some(inner_body);
				}

				trace!(target: "babe", "Checked {:?}; importing.", pre_header);
				telemetry!(
					CONSENSUS_TRACE;
					"babe.checked_and_importing";
					"pre_header" => ?pre_header);

				let mut import_block = BlockImportParams::new(origin, pre_header);
				import_block.post_digests.push(verified_info.seal);
				import_block.body = body;
				import_block.justification = justification;
				import_block.intermediates.insert(
					Cow::from(INTERMEDIATE_KEY),
					Box::new(BabeIntermediate::<Block> { epoch_descriptor }) as Box<dyn Any>,
				);
				import_block.post_hash = Some(hash);

				Ok((import_block, Default::default()))
			}
			CheckedHeader::Deferred(a, b) => {
				debug!(target: "babe", "Checking {:?} failed; {:?}, {:?}.", hash, a, b);
				telemetry!(CONSENSUS_DEBUG; "babe.header_too_far_in_future";
					"hash" => ?hash, "a" => ?a, "b" => ?b
				);
				Err(Error::<Block>::TooFarInFuture(hash).into())
			}
		}
	}
}

/// The BABE import queue type.
pub type BabeImportQueue<B, Transaction> = BasicQueue<B, Transaction>;

/// Register the babe inherent data provider, if not registered already.
fn register_babe_inherent_data_provider(
	inherent_data_providers: &InherentDataProviders,
	slot_duration: u64,
) -> Result<(), sp_consensus::Error> {
	debug!(target: "babe", "Registering");
	if !inherent_data_providers.has_provider(&sp_consensus_babe::inherents::INHERENT_IDENTIFIER) {
		inherent_data_providers
			.register_provider(sp_consensus_babe::inherents::InherentDataProvider::new(slot_duration))
			.map_err(Into::into)
			.map_err(sp_consensus::Error::InherentData)
	} else {
		Ok(())
	}
}

/// A block-import handler for BABE.
///
/// This scans each imported block for epoch change signals. The signals are
/// tracked in a tree (of all forks), and the import logic validates all epoch
/// change transitions, i.e. whether a given epoch change is expected or whether
/// it is missing.
///
/// The epoch change tree should be pruned as blocks are finalized.
pub struct BabeBlockImport<Block: BlockT, Client, I> {
	inner: I,
	client: Arc<Client>,
	epoch_changes: SharedEpochChanges<Block, Epoch>,
	config: Config,
}

impl<Block: BlockT, I: Clone, Client> Clone for BabeBlockImport<Block, Client, I> {
	fn clone(&self) -> Self {
		BabeBlockImport {
			inner: self.inner.clone(),
			client: self.client.clone(),
			epoch_changes: self.epoch_changes.clone(),
			config: self.config.clone(),
		}
	}
}

impl<Block: BlockT, Client, I> BabeBlockImport<Block, Client, I> {
	fn new(
		client: Arc<Client>,
		epoch_changes: SharedEpochChanges<Block, Epoch>,
		block_import: I,
		config: Config,
	) -> Self {
		BabeBlockImport {
			client,
			inner: block_import,
			epoch_changes,
			config,
		}
	}
}

impl<Block, Client, Inner> BlockImport<Block> for BabeBlockImport<Block, Client, Inner> where
	Block: BlockT,
	Inner: BlockImport<Block, Transaction = sp_api::TransactionFor<Client, Block>> + Send + Sync,
	Inner::Error: Into<ConsensusError>,
	Client: HeaderBackend<Block> + HeaderMetadata<Block, Error = sp_blockchain::Error>
		+ AuxStore + ProvideRuntimeApi<Block> + ProvideCache<Block> + Send + Sync,
	Client::Api: BabeApi<Block> + ApiExt<Block>,
{
	type Error = ConsensusError;
	type Transaction = sp_api::TransactionFor<Client, Block>;

	fn import_block(
		&mut self,
		mut block: BlockImportParams<Block, Self::Transaction>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		let hash = block.post_hash();
		let number = block.header.number().clone();

		// early exit if block already in chain, otherwise the check for
		// epoch changes will error when trying to re-import an epoch change
		match self.client.status(BlockId::Hash(hash)) {
			Ok(sp_blockchain::BlockStatus::InChain) => return Ok(ImportResult::AlreadyInChain),
			Ok(sp_blockchain::BlockStatus::Unknown) => {},
			Err(e) => return Err(ConsensusError::ClientImport(e.to_string())),
		}

		let pre_digest = find_pre_digest::<Block>(&block.header)
			.expect("valid babe headers must contain a predigest; \
					 header has been already verified; qed");
		let slot_number = pre_digest.slot_number();

		let parent_hash = *block.header.parent_hash();
		let parent_header = self.client.header(BlockId::Hash(parent_hash))
			.map_err(|e| ConsensusError::ChainLookup(e.to_string()))?
			.ok_or_else(|| ConsensusError::ChainLookup(babe_err(
				Error::<Block>::ParentUnavailable(parent_hash, hash)
			).into()))?;

		let parent_slot = find_pre_digest::<Block>(&parent_header)
			.map(|d| d.slot_number())
			.expect("parent is non-genesis; valid BABE headers contain a pre-digest; \
					header has already been verified; qed");

		// make sure that slot number is strictly increasing
		if slot_number <= parent_slot {
			return Err(
				ConsensusError::ClientImport(babe_err(
					Error::<Block>::SlotNumberMustIncrease(parent_slot, slot_number)
				).into())
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
						babe_err(Error::<Block>::ParentBlockNoAssociatedWeight(hash)).into()
					))?
			};

			let intermediate = block.take_intermediate::<BabeIntermediate<Block>>(
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
		let next_config_digest = find_next_config_digest::<Block>(&block.header)
			.map_err(|e| ConsensusError::ClientImport(e.to_string()))?;

		match (first_in_epoch, next_epoch_digest.is_some(), next_config_digest.is_some()) {
			(true, true, _) => {},
			(false, false, false) => {},
			(false, false, true) => {
				return Err(
					ConsensusError::ClientImport(
						babe_err(Error::<Block>::UnexpectedConfigChange).into(),
					)
				)
			},
			(true, false, _) => {
				return Err(
					ConsensusError::ClientImport(
						babe_err(Error::<Block>::ExpectedEpochChange(hash, slot_number)).into(),
					)
				)
			},
			(false, true, _) => {
				return Err(
					ConsensusError::ClientImport(
						babe_err(Error::<Block>::UnexpectedEpochChange).into(),
					)
				)
			},
		}

		// if there's a pending epoch we'll save the previous epoch changes here
		// this way we can revert it if there's any error
		let mut old_epoch_changes = None;

		let info = self.client.info();

		if let Some(next_epoch_descriptor) = next_epoch_digest {
			old_epoch_changes = Some(epoch_changes.clone());

			let viable_epoch = epoch_changes.viable_epoch(
				&epoch_descriptor,
				|slot| Epoch::genesis(&self.config, slot)
			).ok_or_else(|| {
				ConsensusError::ClientImport(Error::<Block>::FetchEpoch(parent_hash).into())
			})?;

			let epoch_config = next_config_digest.map(Into::into).unwrap_or_else(
				|| viable_epoch.as_ref().config.clone()
			);

			// restrict info logging during initial sync to avoid spam
			let log_level = if block.origin == BlockOrigin::NetworkInitialSync {
				log::Level::Debug
			} else {
				log::Level::Info
			};

			log!(target: "babe",
				log_level,
				"👶 New epoch {} launching at block {} (block slot {} >= start slot {}).",
				viable_epoch.as_ref().epoch_index,
				hash,
				slot_number,
				viable_epoch.as_ref().start_slot,
			);

			let next_epoch = viable_epoch.increment((next_epoch_descriptor, epoch_config));

			log!(target: "babe",
				log_level,
				"👶 Next epoch starts at slot {}",
				next_epoch.as_ref().start_slot,
			);

			// prune the tree of epochs not part of the finalized chain or
			// that are not live anymore, and then track the given epoch change
			// in the tree.
			// NOTE: it is important that these operations are done in this
			// order, otherwise if pruning after import the `is_descendent_of`
			// used by pruning may not know about the block that is being
			// imported.
			let prune_and_import = || {
				prune_finalized(
					self.client.clone(),
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
				debug!(target: "babe", "Failed to launch next epoch: {:?}", e);
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
fn prune_finalized<Block, Client>(
	client: Arc<Client>,
	epoch_changes: &mut EpochChangesFor<Block, Epoch>,
) -> Result<(), ConsensusError> where
	Block: BlockT,
	Client: HeaderBackend<Block> + HeaderMetadata<Block, Error = sp_blockchain::Error>,
{
	let info = client.info();

	let finalized_slot = {
		let finalized_header = client.header(BlockId::Hash(info.finalized_hash))
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

/// Produce a BABE block-import object to be used later on in the construction of
/// an import-queue.
///
/// Also returns a link object used to correctly instantiate the import queue
/// and background worker.
pub fn block_import<Client, Block: BlockT, I>(
	config: Config,
	wrapped_block_import: I,
	client: Arc<Client>,
) -> ClientResult<(BabeBlockImport<Block, Client, I>, BabeLink<Block>)> where
	Client: AuxStore + HeaderBackend<Block> + HeaderMetadata<Block, Error = sp_blockchain::Error>,
{
	let epoch_changes = aux_schema::load_epoch_changes::<Block, _>(&*client, &config)?;
	let link = BabeLink {
		epoch_changes: epoch_changes.clone(),
		time_source: Default::default(),
		config: config.clone(),
	};

	// NOTE: this isn't entirely necessary, but since we didn't use to prune the
	// epoch tree it is useful as a migration, so that nodes prune long trees on
	// startup rather than waiting until importing the next epoch change block.
	prune_finalized(
		client.clone(),
		&mut epoch_changes.lock(),
	)?;

	let import = BabeBlockImport::new(
		client,
		epoch_changes,
		wrapped_block_import,
		config,
	);

	Ok((import, link))
}

/// Start an import queue for the BABE consensus algorithm.
///
/// This method returns the import queue, some data that needs to be passed to the block authoring
/// logic (`BabeLink`), and a future that must be run to
/// completion and is responsible for listening to finality notifications and
/// pruning the epoch changes tree.
///
/// The block import object provided must be the `BabeBlockImport` or a wrapper
/// of it, otherwise crucial import logic will be omitted.
pub fn import_queue<Block: BlockT, Client, Inner>(
	babe_link: BabeLink<Block>,
	block_import: Inner,
	justification_import: Option<BoxJustificationImport<Block>>,
	finality_proof_import: Option<BoxFinalityProofImport<Block>>,
	client: Arc<Client>,
	inherent_data_providers: InherentDataProviders,
) -> ClientResult<BabeImportQueue<Block, sp_api::TransactionFor<Client, Block>>> where
	Inner: BlockImport<Block, Error = ConsensusError, Transaction = sp_api::TransactionFor<Client, Block>>
		+ Send + Sync + 'static,
	Client: ProvideRuntimeApi<Block> + ProvideCache<Block> + Send + Sync + AuxStore + 'static,
	Client: HeaderBackend<Block> + HeaderMetadata<Block, Error = sp_blockchain::Error>,
	Client::Api: BlockBuilderApi<Block> + BabeApi<Block> + ApiExt<Block, Error = sp_blockchain::Error>,
{
	register_babe_inherent_data_provider(&inherent_data_providers, babe_link.config.slot_duration)?;

	let verifier = BabeVerifier {
		client: client.clone(),
		inherent_data_providers,
		config: babe_link.config,
		epoch_changes: babe_link.epoch_changes,
		time_source: babe_link.time_source,
	};

	Ok(BasicQueue::new(
		verifier,
		Box::new(block_import),
		justification_import,
		finality_proof_import,
	))
}

/// BABE test helpers. Utility methods for manually authoring blocks.
#[cfg(feature = "test-helpers")]
pub mod test_helpers {
	use super::*;

	/// Try to claim the given slot and return a `BabePreDigest` if
	/// successful.
	pub fn claim_slot<B, C>(
		slot_number: u64,
		parent: &B::Header,
		client: &C,
		keystore: &KeyStorePtr,
		link: &BabeLink<B>,
	) -> Option<PreDigest> where
		B: BlockT,
		C: ProvideRuntimeApi<B> +
			ProvideCache<B> +
			HeaderBackend<B> +
			HeaderMetadata<B, Error = ClientError>,
		C::Api: BabeApi<B>,
	{
		let epoch_changes = link.epoch_changes.lock();
		let epoch = epoch_changes.epoch_data_for_child_of(
			descendent_query(client),
			&parent.hash(),
			parent.number().clone(),
			slot_number,
			|slot| Epoch::genesis(&link.config, slot),
		).unwrap().unwrap();

		authorship::claim_slot(
			slot_number,
			&epoch,
			keystore,
		).map(|(digest, _)| digest)
	}
}
