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
//! The fork choice rule is weight-based, where weight equals the number of
//! primary blocks in the chain. We will pick the heaviest chain (more primary
//! blocks) and will go with the longest one in case of a tie.
//!
//! An in-depth description and analysis of the protocol can be found here:
//! <https://research.web3.foundation/en/latest/polkadot/BABE/Babe>

#![forbid(unsafe_code)]
#![warn(missing_docs)]
pub use babe_primitives::*;
pub use consensus_common::SyncOracle;
use std::{collections::HashMap, sync::Arc, u64, pin::Pin, time::{Instant, Duration}};
use babe_primitives;
use consensus_common::ImportResult;
use consensus_common::import_queue::{
	BoxJustificationImport, BoxFinalityProofImport,
};
use consensus_common::well_known_cache_keys::Id as CacheKeyId;
use sr_primitives::{generic::{BlockId, OpaqueDigestItemId}, Justification};
use sr_primitives::traits::{
	Block as BlockT, Header, DigestItemFor, NumberFor, ProvideRuntimeApi,
	Zero,
};
use keystore::KeyStorePtr;
use codec::{Decode, Encode};
use parking_lot::{Mutex, MutexGuard};
use primitives::{blake2_256, Blake2Hasher, H256, Pair, Public, U256};
use merlin::Transcript;
use inherents::{InherentDataProviders, InherentData};
use substrate_telemetry::{
	telemetry,
	CONSENSUS_TRACE,
	CONSENSUS_DEBUG,
};
use schnorrkel::{
	keys::Keypair,
	vrf::{
		VRFProof, VRFInOut, VRFOutput,
	},
};
use consensus_common::{
	self, BlockImport, Environment, Proposer,
	ForkChoiceStrategy, BlockImportParams, BlockOrigin, Error as ConsensusError,
};
use srml_babe::{
	BabeInherentData,
	timestamp::{TimestampInherentData, InherentType as TimestampInherent}
};
use consensus_common::SelectChain;
use consensus_common::import_queue::{Verifier, BasicQueue};
use client::{
	block_builder::api::BlockBuilder as BlockBuilderApi,
	blockchain::{self, HeaderBackend, ProvideCache}, BlockchainEvents, CallExecutor, Client,
	runtime_api::ApiExt, error::Result as ClientResult, backend::{AuxStore, Backend},
	ProvideUncles,
	utils::is_descendent_of,
};
use slots::{CheckedHeader, check_equivocation};
use futures::prelude::*;
use futures01::Stream as _;
use log::{error, warn, debug, info, trace};

use slots::{SlotWorker, SlotData, SlotInfo, SlotCompatible};

mod aux_schema;
mod epoch_changes;
#[cfg(test)]
mod tests;
pub use babe_primitives::{
	AuthorityId, AuthorityPair, AuthoritySignature, Epoch, NextEpochDescriptor,
};
pub use epoch_changes::{EpochChanges, SharedEpochChanges};

/// A slot duration. Create with `get_or_compute`.
// FIXME: Once Rust has higher-kinded types, the duplication between this
// and `super::babe::Config` can be eliminated.
// https://github.com/paritytech/substrate/issues/2434
#[derive(Clone)]
pub struct Config(slots::SlotDuration<BabeConfiguration>);

impl Config {
	/// Either fetch the slot duration from disk or compute it from the genesis
	/// state.
	pub fn get_or_compute<B: BlockT, C>(client: &C) -> ClientResult<Self> where
		C: AuxStore + ProvideRuntimeApi, C::Api: BabeApi<B>,
	{
		trace!(target: "babe", "Getting slot duration");
		match slots::SlotDuration::get_or_compute(client, |a, b| a.configuration(b)).map(Self) {
			Ok(s) => Ok(s),
			Err(s) => {
				warn!(target: "babe", "Failed to get slot duration");
				Err(s)
			}
		}
	}
}

impl std::ops::Deref for Config {
	type Target = BabeConfiguration;

	fn deref(&self) -> &BabeConfiguration {
		&*self.0
	}
}

/// Parameters for BABE.
pub struct BabeParams<B: BlockT, C, E, I, SO, SC> {
	/// The configuration for BABE. Includes the slot duration, threshold, and
	/// other parameters.
	pub config: Config,

	/// The keystore that manages the keys of the node.
	pub keystore: KeyStorePtr,

	/// The client to use
	pub client: Arc<C>,

	/// The SelectChain Strategy
	pub select_chain: SC,

	/// A block importer
	pub block_import: I,

	/// The environment
	pub env: E,

	/// A sync oracle
	pub sync_oracle: SO,

	/// Providers for inherent data.
	pub inherent_data_providers: InherentDataProviders,

	/// Force authoring of blocks even if we are offline
	pub force_authoring: bool,

	/// The source of timestamps for relative slots
	pub babe_link: BabeLink<B>,
}

// /// Start the babe worker. The returned future should be run in a tokio runtime.
// pub fn start_babe<B, C, SC, E, I, SO, Error, H>(BabeParams {
// 	config,
// 	client,
// 	keystore,
// 	select_chain,
// 	block_import,
// 	env,
// 	sync_oracle,
// 	inherent_data_providers,
// 	force_authoring,
// 	babe_link,
// }: BabeParams<B, C, E, I, SO, SC>) -> Result<
// 	impl futures01::Future<Item=(), Error=()>,
// 	consensus_common::Error,
// > where
// 	B: BlockT<Header=H>,
// 	C: ProvideRuntimeApi + ProvideCache<B> + ProvideUncles<B> + Send + Sync + 'static,
// 	C::Api: BabeApi<B>,
// 	SC: SelectChain<B> + 'static,
// 	E: Environment<B, Error=Error> + Send + Sync,
// 	E::Proposer: Proposer<B, Error=Error>,
// 	<E::Proposer as Proposer<B>>::Create: Unpin + Send + 'static,
// 	H: Header<Hash=B::Hash>,
// 	I: BlockImport<B> + Send + Sync + 'static,
// 	Error: std::error::Error + Send + From<::consensus_common::Error> + From<I::Error> + 'static,
// 	SO: SyncOracle + Send + Sync + Clone,
// {
// 	let worker = BabeWorker {
// 		client: client.clone(),
// 		block_import: Arc::new(Mutex::new(block_import)),
// 		env,
// 		sync_oracle: sync_oracle.clone(),
// 		force_authoring,
// 		c: config.c(),
// 		keystore,
// 		epoch_changes: babe_link.epoch_changes.clone(),
// 	};
// 	register_babe_inherent_data_provider(&inherent_data_providers, config.0.slot_duration())?;
// 	uncles::register_uncles_inherent_data_provider(
// 		client.clone(),
// 		select_chain.clone(),
// 		&inherent_data_providers,
// 	)?;
// 	Ok(slots::start_slot_worker(
// 		config.0,
// 		select_chain,
// 		worker,
// 		sync_oracle,
// 		inherent_data_providers,
// 		babe_link,
// 	).map(|()| Ok::<(), ()>(())).compat())
// }

struct BabeWorker<B: BlockT, C, E, I, SO> {
	client: Arc<C>,
	block_import: Arc<Mutex<I>>,
	env: E,
	sync_oracle: SO,
	force_authoring: bool,
	c: (u64, u64),
	keystore: KeyStorePtr,
	epoch_changes: SharedEpochChanges<B>,
}

// impl<H, B, C, E, I, Error, SO> slots::SimpleSlotWorker<B> for BabeWorker<B, C, E, I, SO> where
// 	B: BlockT<Header=H>,
// 	C: ProvideRuntimeApi + ProvideCache<B>,
// 	C::Api: BabeApi<B>,
// 	E: Environment<B, Error=Error>,
// 	E::Proposer: Proposer<B, Error=Error>,
// 	<E::Proposer as Proposer<B>>::Create: Unpin + Send + 'static,
// 	H: Header<Hash=B::Hash>,
// 	I: BlockImport<B> + Send + Sync + 'static,
// 	SO: SyncOracle + Send + Clone,
// 	Error: std::error::Error + Send + From<::consensus_common::Error> + From<I::Error> + 'static,
// {
// 	type EpochData = Epoch;
// 	type Claim = (BabePreDigest, AuthorityPair);
// 	type SyncOracle = SO;
// 	type Proposer = E::Proposer;
// 	type BlockImport = I;

// 	fn logging_target(&self) -> &'static str {
// 		"babe"
// 	}

// 	fn block_import(&self) -> Arc<Mutex<Self::BlockImport>> {
// 		self.block_import.clone()
// 	}

// 	fn epoch_data(&self, parent: &B::Header, slot_number: u64) -> Result<Self::EpochData, consensus_common::Error> {
// 		epoch(
// 			self.client.as_ref(),
// 			parent.hash(),
// 			parent.number().clone(),
// 			slot_number,
// 			&self.epoch_changes,
// 		)
// 			.ok_or(consensus_common::Error::InvalidAuthoritiesSet)
// 	}

// 	fn authorities_len(&self, epoch_data: &Self::EpochData) -> usize {
// 		epoch_data.authorities.len()
// 	}

// 	fn claim_slot(
// 		&self,
// 		header: &B::Header,
// 		slot_number: u64,
// 		epoch_data: &Self::EpochData,
// 	) -> Option<Self::Claim> {
// 		let parent_weight = {
// 			let pre_digest = find_pre_digest::<B>(&header).ok()?;
// 			pre_digest.weight()
// 		};

// 		claim_slot(
// 			slot_number,
// 			parent_weight,
// 			epoch_data,
// 			self.c,
// 			&self.keystore,
// 		)
// 	}

// 	fn pre_digest_data(&self, _slot_number: u64, claim: &Self::Claim) -> Vec<sr_primitives::DigestItem<B::Hash>> {
// 		vec![
// 			<DigestItemFor<B> as CompatibleDigestItem>::babe_pre_digest(claim.0.clone()),
// 		]
// 	}

// 	fn import_block(&self) -> Box<dyn Fn(
// 		B::Header,
// 		&B::Hash,
// 		Vec<B::Extrinsic>,
// 		Self::Claim,
// 	) -> consensus_common::BlockImportParams<B> + Send> {
// 		Box::new(|header, header_hash, body, (_, pair)| {
// 			// sign the pre-sealed hash of the block and then
// 			// add it to a digest item.
// 			let signature = pair.sign(header_hash.as_ref());
// 			let signature_digest_item = <DigestItemFor<B> as CompatibleDigestItem>::babe_seal(signature);

// 			// When we building our own blocks we always author on top of the
// 			// current best according to `SelectChain`, therefore our own block
// 			// proposal should always become the new best.
// 			BlockImportParams {
// 				origin: BlockOrigin::Own,
// 				header,
// 				justification: None,
// 				post_digests: vec![signature_digest_item],
// 				body: Some(body),
// 				finalized: false,
// 				auxiliary: Vec::new(),
// 				fork_choice: ForkChoiceStrategy::Custom(true),
// 			}
// 		})
// 	}

// 	fn force_authoring(&self) -> bool {
// 		self.force_authoring
// 	}

// 	fn sync_oracle(&mut self) -> &mut Self::SyncOracle {
// 		&mut self.sync_oracle
// 	}

// 	fn proposer(&mut self, block: &B::Header) -> Result<Self::Proposer, consensus_common::Error> {
// 		self.env.init(block).map_err(|e| {
// 			consensus_common::Error::ClientImport(format!("{:?}", e)).into()
// 		})
// 	}
// }

// impl<H, B, C, E, I, Error, SO> SlotWorker<B> for BabeWorker<B, C, E, I, SO> where
// 	B: BlockT<Header=H>,
// 	C: ProvideRuntimeApi + ProvideCache<B> + Send + Sync,
// 	C::Api: BabeApi<B>,
// 	E: Environment<B, Error=Error> + Send + Sync,
// 	E::Proposer: Proposer<B, Error=Error>,
// 	<E::Proposer as Proposer<B>>::Create: Unpin + Send + 'static,
// 	H: Header<Hash=B::Hash>,
// 	I: BlockImport<B> + Send + Sync + 'static,
// 	SO: SyncOracle + Send + Sync + Clone,
// 	Error: std::error::Error + Send + From<::consensus_common::Error> + From<I::Error> + 'static,
// {
// 	type OnSlot = Pin<Box<dyn Future<Output = Result<(), consensus_common::Error>> + Send>>;

// 	fn on_slot(&mut self, chain_head: B::Header, slot_info: SlotInfo) -> Self::OnSlot {
// 		<Self as slots::SimpleSlotWorker<B>>::on_slot(self, chain_head, slot_info)
// 	}
// }

macro_rules! babe_err {
	($($i: expr),+) => {
		{ debug!(target: "babe", $($i),+)
		; format!($($i),+)
		}
	};
}

/// Extract the BABE pre digest from the given header. Pre-runtime digests are
/// mandatory, the function will return `Err` if none is found.
fn find_pre_digest<B: BlockT>(header: &B::Header) -> Result<BabePreDigest, String>
	where DigestItemFor<B>: CompatibleDigestItem,
{
	// genesis block doesn't contain a pre digest so let's generate a
	// dummy one to not break any invariants in the rest of the code
	if header.number().is_zero() {
		return Ok(BabePreDigest::Secondary {
			slot_number: 0,
			authority_index: 0,
		});
	}

	let mut pre_digest: Option<_> = None;
	for log in header.digest().logs() {
		trace!(target: "babe", "Checking log {:?}, looking for pre runtime digest", log);
		match (log.as_babe_pre_digest(), pre_digest.is_some()) {
			(Some(_), true) => Err(babe_err!("Multiple BABE pre-runtime digests, rejecting!"))?,
			(None, _) => trace!(target: "babe", "Ignoring digest not meant for us"),
			(s, false) => pre_digest = s,
		}
	}
	pre_digest.ok_or_else(|| babe_err!("No BABE pre-runtime digest found"))
}

/// Extract the BABE epoch change digest from the given header, if it exists.
fn find_next_epoch_digest<B: BlockT>(header: &B::Header)
	-> Result<Option<NextEpochDescriptor>, String>
	where DigestItemFor<B>: CompatibleDigestItem,
{
	let mut epoch_digest: Option<_> = None;
	for log in header.digest().logs() {
		trace!(target: "babe", "Checking log {:?}, looking for epoch change digest.", log);
		let log = log.try_to::<ConsensusLog>(OpaqueDigestItemId::Consensus(&BABE_ENGINE_ID));
		match (log, epoch_digest.is_some()) {
			(Some(ConsensusLog::NextEpochData(_)), true) => Err(babe_err!("Multiple BABE epoch change digests, rejecting!"))?,
			(Some(ConsensusLog::NextEpochData(epoch)), false) => epoch_digest = Some(epoch),
			_ => trace!(target: "babe", "Ignoring digest not meant for us"),
		}
	}

	Ok(epoch_digest)
}

struct VerificationParams<'a, B: 'a + BlockT> {
	/// the header being verified.
	header: B::Header,
	/// the pre-digest of the header being verified. this is optional - if prior
	/// verification code had to read it, it can be included here to avoid duplicate
	/// work.
	pre_digest: Option<BabePreDigest>,
	/// The total weight of the chain indicated by the parent block.
	parent_weight: BabeBlockWeight,
	/// the slot number of the current time.
	slot_now: SlotNumber,
	/// epoch descriptor of the epoch this block _should_ be under, if it's valid.
	epoch: &'a Epoch,
	/// genesis config of this BABE chain.
	config: &'a Config,
}

struct VerifiedHeaderInfo<B: BlockT> {
	pre_digest: DigestItemFor<B>,
	seal: DigestItemFor<B>,
	weight: BabeBlockWeight,
}

/// Check a header has been signed by the right key. If the slot is too far in
/// the future, an error will be returned. If successful, returns the pre-header
/// and the digest item containing the seal.
///
/// The seal must be the last digest.  Otherwise, the whole header is considered
/// unsigned.  This is required for security and must not be changed.
///
/// This digest item will always return `Some` when used with `as_babe_pre_digest`.
///
/// The given header can either be from a primary or secondary slot assignment,
/// with each having different validation logic.
fn check_header<B: BlockT + Sized, C: AuxStore>(
	params: VerificationParams<B>,
	client: &C,
) -> Result<CheckedHeader<B::Header, VerifiedHeaderInfo<B>>, String> where
	DigestItemFor<B>: CompatibleDigestItem,
{
	let VerificationParams {
		mut header,
		pre_digest,
		parent_weight,
		slot_now,
		epoch,
		config,
	} = params;

	let authorities = &epoch.authorities;
	let pre_digest = pre_digest.map(Ok).unwrap_or_else(|| find_pre_digest::<B>(&header))?;

	trace!(target: "babe", "Checking header");
	let seal = match header.digest_mut().pop() {
		Some(x) => x,
		None => return Err(babe_err!("Header {:?} is unsealed", header.hash())),
	};

	let sig = seal.as_babe_seal().ok_or_else(|| {
		babe_err!("Header {:?} has a bad seal", header.hash())
	})?;

	// the pre-hash of the header doesn't include the seal
	// and that's what we sign
	let pre_hash = header.hash();

	if pre_digest.slot_number() > slot_now {
		header.digest_mut().push(seal);
		return Ok(CheckedHeader::Deferred(header, pre_digest.slot_number()));
	}

	if pre_digest.authority_index() > authorities.len() as u32 {
		return Err(babe_err!("Slot author not found"));
	}

	let weight = match &pre_digest {
		BabePreDigest::Primary { vrf_output, vrf_proof, authority_index, slot_number } => {
			debug!(target: "babe", "Verifying Primary block");

			let digest = (vrf_output, vrf_proof, *authority_index, *slot_number);

			check_primary_header::<B>(
				pre_hash,
				digest,
				sig,
				&epoch,
				config.c,
			)?;

			parent_weight + 1
		},
		BabePreDigest::Secondary { authority_index, slot_number } if config.secondary_slots => {
			debug!(target: "babe", "Verifying Secondary block");

			let digest = (*authority_index, *slot_number);

			check_secondary_header::<B>(
				pre_hash,
				digest,
				sig,
				&epoch,
			)?;

			parent_weight
		},
		_ => {
			return Err(babe_err!("Secondary slot assignments are disabled for the current epoch."));
		}
	};

	// TODO: write weight to disk (here or in calling function?)

	let author = &authorities[pre_digest.authority_index() as usize].0;

	// the header is valid but let's check if there was something else already
	// proposed at the same slot by the given author
	if let Some(equivocation_proof) = check_equivocation(
		client,
		slot_now,
		pre_digest.slot_number(),
		&header,
		author,
	).map_err(|e| e.to_string())? {
		info!(
			"Slot author {:?} is equivocating at slot {} with headers {:?} and {:?}",
			author,
			pre_digest.slot_number(),
			equivocation_proof.fst_header().hash(),
			equivocation_proof.snd_header().hash(),
		);
	}

	let info = VerifiedHeaderInfo {
		pre_digest: CompatibleDigestItem::babe_pre_digest(pre_digest),
		seal,
		weight,
	};
	Ok(CheckedHeader::Checked(header, info))
}

/// Check a primary slot proposal header. We validate that the given header is
/// properly signed by the expected authority, and that the contained VRF proof
/// is valid. Additionally, the weight of this block must increase compared to
/// its parent since it is a primary block.
fn check_primary_header<B: BlockT + Sized>(
	pre_hash: B::Hash,
	pre_digest: (&VRFOutput, &VRFProof, AuthorityIndex, SlotNumber),
	signature: AuthoritySignature,
	epoch: &Epoch,
	c: (u64, u64),
) -> Result<(), String>
	where DigestItemFor<B>: CompatibleDigestItem,
{
	let (vrf_output, vrf_proof, authority_index, slot_number) = pre_digest;

	let author = &epoch.authorities[authority_index as usize].0;

	if AuthorityPair::verify(&signature, pre_hash, &author) {
		let (inout, _) = {
			let transcript = make_transcript(
				&epoch.randomness,
				slot_number,
				epoch.epoch_index,
			);

			schnorrkel::PublicKey::from_bytes(author.as_slice()).and_then(|p| {
				p.vrf_verify(transcript, vrf_output, vrf_proof)
			}).map_err(|s| {
				babe_err!("VRF verification failed: {:?}", s)
			})?
		};

		let threshold = calculate_primary_threshold(
			c,
			&epoch.authorities,
			authority_index as usize,
		);

		if !check_primary_threshold(&inout, threshold) {
			return Err(babe_err!("VRF verification of block by author {:?} failed: \
								  threshold {} exceeded", author, threshold));
		}

		Ok(())
	} else {
		Err(babe_err!("Bad signature on {:?}", pre_hash))
	}
}

/// Check a secondary slot proposal header. We validate that the given header is
/// properly signed by the expected authority, which we have a deterministic way
/// of computing. Additionally, the weight of this block must stay the same
/// compared to its parent since it is a secondary block.
fn check_secondary_header<B: BlockT>(
	pre_hash: B::Hash,
	pre_digest: (AuthorityIndex, SlotNumber),
	signature: AuthoritySignature,
	epoch: &Epoch,
) -> Result<(), String> {
	let (authority_index, slot_number) = pre_digest;

	// check the signature is valid under the expected authority and
	// chain state.
	let expected_author = secondary_slot_author(
		slot_number,
		&epoch.authorities,
		epoch.randomness,
	).ok_or_else(|| "No secondary author expected.".to_string())?;

	let author = &epoch.authorities[authority_index as usize].0;

	if expected_author != author {
		let msg = format!("Invalid author: Expected secondary author: {:?}, got: {:?}.",
			expected_author,
			author,
		);

		return Err(msg);
	}

	if AuthorityPair::verify(&signature, pre_hash.as_ref(), author) {
		Ok(())
	} else {
		Err(format!("Bad signature on {:?}", pre_hash))
	}
}

/// State that must be shared between the import queue and the authoring logic.
#[derive(Clone)]
pub struct BabeLink<Block: BlockT> {
	time_source: Arc<Mutex<(Option<Duration>, Vec<(Instant, u64)>)>>,
	epoch_changes: SharedEpochChanges<Block>,
}

impl<Block: BlockT> SlotCompatible for BabeLink<Block> {
	fn extract_timestamp_and_slot(
		&self,
		data: &InherentData,
	) -> Result<(TimestampInherent, u64, std::time::Duration), consensus_common::Error> {
		trace!(target: "babe", "extract timestamp");
		data.timestamp_inherent_data()
			.and_then(|t| data.babe_inherent_data().map(|a| (t, a)))
			.map_err(Into::into)
			.map_err(consensus_common::Error::InherentData)
			.map(|(x, y)| (x, y, self.time_source.lock().0.take().unwrap_or_default()))
	}
}

/// A verifier for Babe blocks.
pub struct BabeVerifier<B, E, Block: BlockT, RA, PRA, T> {
	client: Arc<Client<B, E, Block, RA>>,
	api: Arc<PRA>,
	inherent_data_providers: inherents::InherentDataProviders,
	config: Config,
	babe_link: BabeLink<Block>,
	transaction_pool: Option<Arc<T>>,
}

impl<B, E, Block: BlockT, RA, PRA, T> BabeVerifier<B, E, Block, RA, PRA, T> {
	fn check_inherents(
		&self,
		block: Block,
		block_id: BlockId<Block>,
		inherent_data: InherentData,
	) -> Result<(), String>
		where PRA: ProvideRuntimeApi, PRA::Api: BlockBuilderApi<Block>
	{
		let inherent_res = self.api.runtime_api().check_inherents(
			&block_id,
			block,
			inherent_data,
		).map_err(|e| format!("{:?}", e))?;

		if !inherent_res.ok() {
			inherent_res
				.into_errors()
				.try_for_each(|(i, e)| {
					Err(self.inherent_data_providers.error_to_string(&i, &e))
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
				.checked_mul(1_000_000u128) // self.config.get() returns *milliseconds*
				.and_then(|x| {
					x.checked_mul(u128::from(slot_number).saturating_sub(u128::from(sl)))
				})
				.expect("we cannot have timespans long enough for this to overflow; qed");

			const NANOS_PER_SEC: u32 = 1_000_000_000;
			let nanos = (offset % u128::from(NANOS_PER_SEC)) as u32;
			let secs = (offset / u128::from(NANOS_PER_SEC)) as u64;

			t + Duration::new(secs, nanos)
		}).collect();

		// FIXME #2926: use a selection algorithm instead of a full sorting algorithm.
		new_list.sort_unstable();

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

impl<B, E, Block, RA, PRA, T> Verifier<Block> for BabeVerifier<B, E, Block, RA, PRA, T> where
	Block: BlockT<Hash=H256>,
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
	RA: Send + Sync,
	PRA: ProvideRuntimeApi + Send + Sync + AuxStore + ProvideCache<Block>,
	PRA::Api: BlockBuilderApi<Block> + BabeApi<Block>,
	T: Send + Sync + 'static,
{
	fn verify(
		&mut self,
		origin: BlockOrigin,
		header: Block::Header,
		justification: Option<Justification>,
		mut body: Option<Vec<Block::Extrinsic>>,
	) -> Result<(BlockImportParams<Block>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
		use sr_primitives::traits::One;

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
			.map_err(String::from)?;

		let (_, slot_now, _) = self.babe_link.extract_timestamp_and_slot(&inherent_data)
			.map_err(|e| format!("Could not extract timestamp and slot: {:?}", e))?;

		let hash = header.hash();
		let parent_hash = *header.parent_hash();

		let parent_header = self.client.header(&BlockId::Hash(parent_hash))
			.map_err(|e| format!("Could not fetch parent header {:?}: {:?}", parent_hash, e))?
			.ok_or_else(|| format!("Parent header {:?} not found.", parent_hash))?;

		let pre_digest = find_pre_digest::<Block>(&header)?;

		// TODO: Get epoch for header we're verifying.
		// let epoch = epoch(
		// 	self.api.as_ref(),
		// 	parent_hash,
		// 	parent_header.number().clone(),
		// 	pre_digest.slot_number(),
		// 	&self.babe_link.epoch_changes,
		// )
		// 	.ok_or_else(|| format!("Could not fetch epoch at {:?}", parent_hash))?;
		let epoch = unimplemented!();

		// load parent weight, special-casing the genesis.
		let parent_weight = aux_schema::load_block_weight(&*self.client, parent_hash)
			.map_err(|e| e.to_string())?
			.or(if header.number() == &One::one() { Some(0) } else { None })
			.ok_or_else(
				|| format!("No block weight for parent header.")
			)?;

		// We add one to the current slot to allow for some small drift.
		// FIXME #1019 in the future, alter this queue to allow deferring of headers
		let v_params = VerificationParams {
			header,
			pre_digest: Some(pre_digest.clone()),
			parent_weight,
			slot_now,
			epoch: &epoch,
			config: &self.config,
		};
		let checked_header = check_header::<Block, PRA>(v_params, &self.api)?;

		match checked_header {
			CheckedHeader::Checked(pre_header, verified_info) => {
				let babe_pre_digest = verified_info.pre_digest.as_babe_pre_digest()
					.expect("check_header always returns a pre-digest digest item; qed");

				let slot_number = babe_pre_digest.slot_number();

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

				// The fork choice rule is that we pick the heaviest chain (i.e.
				// more primary blocks), if there's a tie we go with the longest
				// chain.
				let new_best = {
					let (last_best, last_best_number) = {
						let info = self.client.info().chain;
						(info.best_hash, info.best_number)
					};

					let last_best_weight = if last_best == parent_hash {
						// the parent=genesis case is already covered for loading parent weight,
						// so we don't need to cover again here.
						parent_weight
					} else {
						aux_schema::load_block_weight(&*self.client, last_best)
							.map_err(|e| e.to_string())?
							.ok_or_else(
								|| format!("No block weight for parent header.")
							)?
					};

					if verified_info.weight > last_best_weight {
						true
					} else if verified_info.weight == last_best_weight {
						*pre_header.number() > last_best_number
					} else {
						false
					}
				};

				let mut auxiliary = Vec::new();

				aux_schema::write_block_weight(
					hash,
					&verified_info.weight,
					|values| auxiliary.extend(
						values.iter().map(|(k, v)| (k.to_vec(), Some(v.to_vec())))
					),
				);

				let import_block = BlockImportParams {
					origin,
					header: pre_header,
					post_digests: vec![verified_info.seal],
					body,
					finalized: false,
					justification,
					auxiliary,
					fork_choice: ForkChoiceStrategy::Custom(new_best),
				};

				Ok((import_block, Default::default()))
			}
			CheckedHeader::Deferred(a, b) => {
				debug!(target: "babe", "Checking {:?} failed; {:?}, {:?}.", hash, a, b);
				telemetry!(CONSENSUS_DEBUG; "babe.header_too_far_in_future";
					"hash" => ?hash, "a" => ?a, "b" => ?b
				);
				Err(format!("Header {:?} rejected: too far in the future", hash))
			}
		}
	}
}

// /// Extract current epoch data from the runtime. Returns `None` if there is
// /// no epoch to draw data from.
// ///
// /// In a chain which does not issue the expected epoch-change digests, this will
// /// return `None`, because there will be no item in the fork-tree.
// fn epoch<B, C>(
// 	client: &C,
// 	parent_hash: B::Hash,
// 	parent_number: NumberFor<B>,
// 	slot_number: SlotNumber,
// 	is_descendent_of: impl Fn(&B::Hash, &B::Hash) -> ClientResult<bool>,
// 	epoch_changes: &SharedEpochChanges<B>,
// ) -> Option<Epoch> where
// 	B: BlockT,
// 	C: ProvideRuntimeApi + ProvideCache<B> + HeaderBackend<B>,
// 	C::Api: BabeApi<B>,
// {

// 	let at = BlockId::Hash(parent_hash);
// 	let epoch = if client.runtime_api().has_api::<dyn BabeApi<B>>(&at).unwrap_or(false) {
// 		let s = BabeApi::epoch(&*client.runtime_api(), &at).ok()?;
// 		if s.authorities.is_empty() {
// 			error!("No authorities!");
// 			None
// 		} else {
// 			Some(s)
// 		}
// 	} else {
// 		error!("bad api!");
// 		None
// 	};
// 	let epoch = epoch?;

// 	epoch_changes.lock().epoch_for_child_of(
// 		&parent_hash,
// 		&parent_number,
// 		slot_number,
// 	)
// }

/// The BABE import queue type.
pub type BabeImportQueue<B> = BasicQueue<B>;

/// Register the babe inherent data provider, if not registered already.
fn register_babe_inherent_data_provider(
	inherent_data_providers: &InherentDataProviders,
	slot_duration: u64,
) -> Result<(), consensus_common::Error> {
	debug!(target: "babe", "Registering");
	if !inherent_data_providers.has_provider(&srml_babe::INHERENT_IDENTIFIER) {
		inherent_data_providers
			.register_provider(srml_babe::InherentDataProvider::new(slot_duration))
			.map_err(Into::into)
			.map_err(consensus_common::Error::InherentData)
	} else {
		Ok(())
	}
}

fn get_keypair(q: &AuthorityPair) -> &Keypair {
	use primitives::crypto::IsWrappedBy;
	primitives::sr25519::Pair::from_ref(q).as_ref()
}

#[allow(deprecated)]
fn make_transcript(
	randomness: &[u8],
	slot_number: u64,
	epoch: u64,
) -> Transcript {
	let mut transcript = Transcript::new(&BABE_ENGINE_ID);
	transcript.commit_bytes(b"slot number", &slot_number.to_le_bytes());
	transcript.commit_bytes(b"current epoch", &epoch.to_le_bytes());
	transcript.commit_bytes(b"chain randomness", randomness);
	transcript
}

/// Returns true if the given VRF output is lower than the given threshold,
/// false otherwise.
fn check_primary_threshold(inout: &VRFInOut, threshold: u128) -> bool {
	u128::from_le_bytes(inout.make_bytes::<[u8; 16]>(BABE_VRF_PREFIX)) < threshold
}

/// Calculates the primary selection threshold for a given authority, taking
/// into account `c` (`1 - c` represents the probability of a slot being empty).
fn calculate_primary_threshold(
	c: (u64, u64),
	authorities: &[(AuthorityId, BabeAuthorityWeight)],
	authority_index: usize,
) -> u128 {
	use num_bigint::BigUint;
	use num_rational::BigRational;
	use num_traits::{cast::ToPrimitive, identities::One};

	let c = c.0 as f64 / c.1 as f64;

	let theta =
		authorities[authority_index].1 as f64 /
		authorities.iter().map(|(_, weight)| weight).sum::<u64>() as f64;

	let calc = || {
		let p = BigRational::from_float(1f64 - (1f64 - c).powf(theta))?;
		let numer = p.numer().to_biguint()?;
		let denom = p.denom().to_biguint()?;
		((BigUint::one() << 128) * numer / denom).to_u128()
	};

	calc().unwrap_or(u128::max_value())
}

/// Tries to claim the given slot number. This method starts by trying to claim
/// a primary VRF based slot. If we are not able to claim it, then if we have
/// secondary slots enabled for the given epoch, we will fallback to trying to
/// claim a secondary slot.
fn claim_slot(
	slot_number: SlotNumber,
	epoch: &Epoch,
	config: &Config,
	c: (u64, u64),
	keystore: &KeyStorePtr,
) -> Option<(BabePreDigest, AuthorityPair)> {
	claim_primary_slot(slot_number, epoch, c, keystore)
		.or_else(|| {
			if config.secondary_slots {
				claim_secondary_slot(
					slot_number,
					&epoch.authorities,
					keystore,
					epoch.randomness,
				)
			} else {
				None
			}
		})
}

/// Claim a primary slot if it is our turn.  Returns `None` if it is not our turn.
/// This hashes the slot number, epoch, genesis hash, and chain randomness into
/// the VRF.  If the VRF produces a value less than `threshold`, it is our turn,
/// so it returns `Some(_)`. Otherwise, it returns `None`.
fn claim_primary_slot(
	slot_number: SlotNumber,
	epoch: &Epoch,
	c: (u64, u64),
	keystore: &KeyStorePtr,
) -> Option<(BabePreDigest, AuthorityPair)> {
	let Epoch { authorities, randomness, epoch_index, .. } = epoch;
	let keystore = keystore.read();

	for (pair, authority_index) in authorities.iter()
		.enumerate()
		.flat_map(|(i, a)| {
			keystore.key_pair::<AuthorityPair>(&a.0).ok().map(|kp| (kp, i))
		})
	{
		let transcript = make_transcript(randomness, slot_number, *epoch_index);

		// Compute the threshold we will use.
		//
		// We already checked that authorities contains `key.public()`, so it can't
		// be empty.  Therefore, this division in `calculate_threshold` is safe.
		let threshold = calculate_primary_threshold(c, authorities, authority_index);

		let pre_digest = get_keypair(&pair)
			.vrf_sign_after_check(transcript, |inout| check_primary_threshold(inout, threshold))
			.map(|s| {
				BabePreDigest::Primary {
					slot_number,
					vrf_output: s.0.to_output(),
					vrf_proof: s.1,
					authority_index: authority_index as u32,
				}
			});

		// early exit on first successful claim
		if let Some(pre_digest) = pre_digest {
			return Some((pre_digest, pair));
		}
	}

	None
}

/// Get the expected secondary author for the given slot and with given
/// authorities. This should always assign the slot to some authority unless the
/// authorities list is empty.
fn secondary_slot_author(
	slot_number: u64,
	authorities: &[(AuthorityId, BabeAuthorityWeight)],
	randomness: [u8; 32],
) -> Option<&AuthorityId> {
	if authorities.is_empty() {
		return None;
	}

	let rand = U256::from((randomness, slot_number).using_encoded(blake2_256));

	let authorities_len = U256::from(authorities.len());
	let idx = rand % authorities_len;

	let expected_author = authorities.get(idx.as_u32() as usize)
		.expect("authorities not empty; index constrained to list length; \
				this is a valid index; qed");

	Some(&expected_author.0)
}

/// Claim a secondary slot if it is our turn to propose, returning the
/// pre-digest to use when authoring the block, or `None` if it is not our turn
/// to propose.
fn claim_secondary_slot(
	slot_number: SlotNumber,
	authorities: &[(AuthorityId, BabeAuthorityWeight)],
	keystore: &KeyStorePtr,
	randomness: [u8; 32],
) -> Option<(BabePreDigest, AuthorityPair)> {
	if authorities.is_empty() {
		return None;
	}

	let expected_author = secondary_slot_author(
		slot_number,
		authorities,
		randomness,
	)?;

	let keystore = keystore.read();

	for (pair, authority_index) in authorities.iter()
		.enumerate()
		.flat_map(|(i, a)| {
			keystore.key_pair::<AuthorityPair>(&a.0).ok().map(|kp| (kp, i))
		})
	{
		if pair.public() == *expected_author {
			let pre_digest = BabePreDigest::Secondary {
				slot_number,
				authority_index: authority_index as u32,
			};

			return Some((pre_digest, pair));
		}
	}

	None
}

/// A block-import handler for BABE.
///
/// This scans each imported block for epoch change signals. The signals are
/// tracked in a tree (of all forks), and the import logic validates all epoch
/// change transitions, i.e. whether a given epoch change is expected or whether
/// it is missing.
///
/// The epoch change tree should be pruned as blocks are finalized.
pub struct BabeBlockImport<B, E, Block: BlockT, I, RA, PRA> {
	inner: I,
	client: Arc<Client<B, E, Block, RA>>,
	api: Arc<PRA>,
	epoch_changes: SharedEpochChanges<Block>,
	config: Config,
}

impl<B, E, Block: BlockT, I: Clone, RA, PRA> Clone for BabeBlockImport<B, E, Block, I, RA, PRA> {
	fn clone(&self) -> Self {
		BabeBlockImport {
			inner: self.inner.clone(),
			client: self.client.clone(),
			api: self.api.clone(),
			epoch_changes: self.epoch_changes.clone(),
			config: self.config.clone(),
		}
	}
}

impl<B, E, Block: BlockT, I, RA, PRA> BabeBlockImport<B, E, Block, I, RA, PRA> {
	fn new(
		client: Arc<Client<B, E, Block, RA>>,
		api: Arc<PRA>,
		epoch_changes: SharedEpochChanges<Block>,
		block_import: I,
		config: Config,
	) -> Self {
		BabeBlockImport {
			client,
			api,
			inner: block_import,
			epoch_changes,
			config,
		}
	}
}

impl<B, E, Block, I, RA, PRA> BlockImport<Block> for BabeBlockImport<B, E, Block, I, RA, PRA> where
	Block: BlockT<Hash=H256>,
	I: BlockImport<Block> + Send + Sync,
	I::Error: Into<ConsensusError>,
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
	RA: Send + Sync,
	PRA: ProvideRuntimeApi + ProvideCache<Block>,
	PRA::Api: BabeApi<Block>,
{
	type Error = ConsensusError;

	fn import_block(
		&mut self,
		mut block: BlockImportParams<Block>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		let hash = block.post_header().hash();
		let number = block.header.number().clone();

		// early exit if block already in chain, otherwise the check for
		// epoch changes will error when trying to re-import an epoch change
		match self.client.status(BlockId::Hash(hash)) {
			Ok(blockchain::BlockStatus::InChain) => return Ok(ImportResult::AlreadyInChain),
			Ok(blockchain::BlockStatus::Unknown) => {},
			Err(e) => return Err(ConsensusError::ClientImport(e.to_string()).into()),
		}

		let slot_number = {
			let pre_digest = find_pre_digest::<Block>(&block.header)
				.expect("valid babe headers must contain a predigest; \
						 header has been already verified; qed");
			pre_digest.slot_number()
		};

		let mut epoch_changes = self.epoch_changes.lock();

		// check if there's any epoch change expected to happen at this slot.
		// `epoch` is the epoch to verify the block under, and `first_in_epoch` is true
		// if this is the first block in its chain for that epoch.
		let (epoch, first_in_epoch) = if number == sr_primitives::traits::One::one() {
			// The first block of the chain is a special-case, since it is
			// implied to kick off the genesis epoch.
			let epoch = Epoch {
				epoch_index: 0,
				start_slot: slot_number,
				duration: self.config.epoch_length,
				authorities: self.config.genesis_authorities.clone(),
				randomness: self.config.randomness.clone(),
			};

			(epoch, true)
		} else {
			let parent_hash = *block.header.parent_hash();
			let parent_header = self.client.header(&BlockId::Hash(parent_hash))
				.map_err(|e| ConsensusError::ChainLookup(e.to_string()))?
				.ok_or_else(|| ConsensusError::ChainLookup(format!(
					"Parent ({}) of {} unavailable. Cannot import",
					parent_hash,
					hash,
				)))?;

			let parent_slot = find_pre_digest::<Block>(&parent_header)
				.map(|d| d.slot_number())
				.expect("parent is non-genesis; valid BABE headers contain a pre-digest; \
						 header has already been verified; qed");

			let epoch = epoch_changes.epoch_for_child_of(
				&parent_hash,
				*parent_header.number(),
				slot_number,
			)
				.ok_or_else(|| ConsensusError::ClientImport(
					format!("Block {} is not valid under any epoch.", hash)
				))?;

			let first_in_epoch = parent_slot < epoch.start_slot;
			(epoch, first_in_epoch)
		};

		// search for this all the time so we can reject unexpected announcements.
		let next_epoch_digest = find_next_epoch_digest::<Block>(&block.header)
			.map_err(|e| ConsensusError::from(ConsensusError::ClientImport(e.to_string())))?;

		match (first_in_epoch, next_epoch_digest.is_some()) {
			(true, true) => {},
			(false, false) => {},
			(true, false) => {
				return Err(
					ConsensusError::ClientImport(
						"Expected epoch change to happen by this block".into(),
					)
				);
			},
			(false, true) => {
				return Err(ConsensusError::ClientImport("Unexpected epoch change".into()));
			},
		}

		// if there's a pending epoch we'll save the previous epoch changes here
		// this way we can revert it if there's any error
		let mut old_epoch_changes = None;

		if let Some(next_epoch_descriptor) = next_epoch_digest {
			let next_epoch = epoch.increment(next_epoch_descriptor);

			old_epoch_changes = Some(epoch_changes.clone());

			// track the epoch change in the fork tree
			epoch_changes.import(
				hash,
				number,
				next_epoch,
			);

			crate::aux_schema::write_epoch_changes::<Block, _, _>(
				&*epoch_changes,
				|insert| block.auxiliary.extend(
					insert.iter().map(|(k, v)| (k.to_vec(), Some(v.to_vec())))
				)
			);
		}

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
		hash: Block::Hash,
		parent_hash: Block::Hash,
	) -> Result<ImportResult, Self::Error> {
		self.inner.check_block(hash, parent_hash).map_err(Into::into)
	}
}

// /// Start an import queue for the BABE consensus algorithm. This method returns
// /// the import queue, some data that needs to be passed to the block authoring
// /// logic (`BabeLink`), a `BabeBlockImport` which should be used by the
// /// authoring when importing its own blocks, and a future that must be run to
// /// completion and is responsible for listening to finality notifications and
// /// pruning the epoch changes tree.
// pub fn import_queue<B, E, Block: BlockT<Hash=H256>, I, RA, PRA, T>(
// 	config: Config,
// 	block_import: I,
// 	justification_import: Option<BoxJustificationImport<Block>>,
// 	finality_proof_import: Option<BoxFinalityProofImport<Block>>,
// 	client: Arc<Client<B, E, Block, RA>>,
// 	api: Arc<PRA>,
// 	inherent_data_providers: InherentDataProviders,
// 	transaction_pool: Option<Arc<T>>,
// ) -> ClientResult<(
// 	BabeImportQueue<Block>,
// 	BabeLink<Block>,
// 	BabeBlockImport<B, E, Block, I, RA, PRA>,
// 	impl futures01::Future<Item = (), Error = ()>,
// )> where
// 	B: Backend<Block, Blake2Hasher> + 'static,
// 	I: BlockImport<Block> + Clone + Send + Sync + 'static,
// 	I::Error: Into<ConsensusError>,
// 	E: CallExecutor<Block, Blake2Hasher> + Clone + Send + Sync + 'static,
// 	RA: Send + Sync + 'static,
// 	PRA: ProvideRuntimeApi + ProvideCache<Block> + Send + Sync + AuxStore + 'static,
// 	PRA::Api: BlockBuilderApi<Block> + BabeApi<Block>,
// 	T: Send + Sync + 'static,
// {
// 	register_babe_inherent_data_provider(&inherent_data_providers, config.get())?;

// 	let babe_link = BabeLink {
// 		time_source: Default::default(),
// 		epoch_changes: aux_schema::load_epoch_changes(&*client)?,
// 	};

// 	let verifier = BabeVerifier {
// 		client: client.clone(),
// 		api: api.clone(),
// 		inherent_data_providers,
// 		babe_link: babe_link.clone(),
// 		config: config.clone(),
// 		transaction_pool,
// 	};

// 	let block_import = BabeBlockImport::new(
// 		client.clone(),
// 		api,
// 		babe_link.epoch_changes.clone(),
// 		block_import,
//		config,
// 	);

// 	let epoch_changes = babe_link.epoch_changes.clone();
// 	let pruning_task = client.finality_notification_stream()
// 		.map(|v| Ok::<_, ()>(v)).compat()
// 		.for_each(move |notification| {
// 			let is_descendent_of = is_descendent_of(&client, None);
// 			epoch_changes.lock().prune(
// 				&notification.hash,
// 				*notification.header.number(),
// 				&is_descendent_of,
// 			).map_err(|e| {
// 				debug!(target: "babe", "Error pruning epoch changes fork tree: {:?}", e)
// 			})?;

// 			Ok(())
// 		});

// 	let babe_link = verifier.babe_link.clone();
// 	let queue = BasicQueue::new(
// 		verifier,
// 		Box::new(block_import.clone()),
// 		justification_import,
// 		finality_proof_import,
// 	);

// 	Ok((queue, babe_link, block_import, pruning_task))
// }

// /// BABE test helpers. Utility methods for manually authoring blocks.
// #[cfg(feature = "test-helpers")]
// pub mod test_helpers {
// 	use super::*;

// 	/// Try to claim the given slot and return a `BabePreDigest` if
// 	/// successful.
// 	pub fn claim_slot<B, C>(
// 		slot_number: u64,
// 		parent: &B::Header,
// 		client: &C,
// 		c: (u64, u64),
// 		keystore: &KeyStorePtr,
// 		link: &BabeLink<B>,
// 	) -> Option<BabePreDigest> where
// 		B: BlockT,
// 		C: ProvideRuntimeApi + ProvideCache<B> + HeaderBackend<B>,
// 		C::Api: BabeApi<B>,
// 	{
// 		let epoch = epoch(
// 			client,
// 			parent.hash(),
// 			parent.number(),
// 			slot_number,
// 			&link.epoch_changes,
// 		).unwrap();

// 		let weight = find_pre_digest::<B>(parent).ok()
// 			.map(|d| d.weight())?;

// 		super::claim_slot(
// 			slot_number,
// 			weight,
// 			&epoch,
// 			c,
// 			keystore,
// 		).map(|(digest, _)| digest)
// 	}
// }
