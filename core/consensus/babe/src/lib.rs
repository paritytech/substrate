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
use sr_primitives::{generic::{BlockId, OpaqueDigestItemId}, Justification};
use sr_primitives::traits::{
	Block as BlockT, Header, DigestItemFor, ProvideRuntimeApi,
	Zero,
};
use keystore::KeyStorePtr;
use parking_lot::Mutex;
use primitives::{Blake2Hasher, H256, Pair};
use inherents::{InherentDataProviders, InherentData};
use substrate_telemetry::{
	telemetry,
	CONSENSUS_TRACE,
	CONSENSUS_DEBUG,
};
use consensus_common::{
	self, BlockImport, Environment, Proposer, BlockCheckParams,
	ForkChoiceStrategy, BlockImportParams, BlockOrigin, Error as ConsensusError,
};
use srml_babe::{
	BabeInherentData,
	timestamp::{TimestampInherentData, InherentType as TimestampInherent}
};
use consensus_common::SelectChain;
use consensus_common::import_queue::{Verifier, BasicQueue, CacheKeyId};
use client::{
	block_builder::api::BlockBuilder as BlockBuilderApi,
	blockchain::{self, HeaderBackend, ProvideCache}, BlockchainEvents, CallExecutor, Client,
	error::Result as ClientResult, error::Error as ClientError, backend::{AuxStore, Backend},
	ProvideUncles,
};
use slots::{CheckedHeader, check_equivocation};
use futures::prelude::*;
use log::{warn, debug, info, trace};
use slots::{SlotWorker, SlotData, SlotInfo, SlotCompatible};
use epoch_changes::descendent_query;
use header_metadata::HeaderMetadata;

mod aux_schema;
mod verification;
mod epoch_changes;
mod authorship;
#[cfg(test)]
mod tests;
pub use babe_primitives::{
	AuthorityId, AuthorityPair, AuthoritySignature, Epoch, NextEpochDescriptor,
};
pub use epoch_changes::{EpochChanges, SharedEpochChanges};

macro_rules! babe_err {
	($($i: expr),+) => {
		{
			debug!(target: "babe", $($i),+);
			format!($($i),+)
		}
	};
}

macro_rules! babe_info {
	($($i: expr),+) => {
		{
			info!(target: "babe", $($i),+);
			format!($($i),+)
		}
	};
}

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
	type Target = BabeConfiguration;

	fn deref(&self) -> &BabeConfiguration {
		&*self.0
	}
}

/// Parameters for BABE.
pub struct BabeParams<B: BlockT, C, E, I, SO, SC> {
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
}

/// Start the babe worker. The returned future should be run in a tokio runtime.
pub fn start_babe<B, C, SC, E, I, SO, Error>(BabeParams {
	keystore,
	client,
	select_chain,
	env,
	block_import,
	sync_oracle,
	inherent_data_providers,
	force_authoring,
	babe_link,
}: BabeParams<B, C, E, I, SO, SC>) -> Result<
	impl futures01::Future<Item=(), Error=()>,
	consensus_common::Error,
> where
	B: BlockT<Hash=H256>,
	C: ProvideRuntimeApi + ProvideCache<B> + ProvideUncles<B> + BlockchainEvents<B>
		+ HeaderBackend<B> + HeaderMetadata<B, Error=ClientError> + Send + Sync + 'static,
	C::Api: BabeApi<B>,
	SC: SelectChain<B> + 'static,
	E: Environment<B, Error=Error> + Send + Sync,
	E::Proposer: Proposer<B, Error=Error>,
	<E::Proposer as Proposer<B>>::Create: Unpin + Send + 'static,
	I: BlockImport<B,Error=ConsensusError> + Send + Sync + 'static,
	Error: std::error::Error + Send + From<::consensus_common::Error> + From<I::Error> + 'static,
	SO: SyncOracle + Send + Sync + Clone,
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
	uncles::register_uncles_inherent_data_provider(
		client.clone(),
		select_chain.clone(),
		&inherent_data_providers,
	)?;

	let epoch_changes = babe_link.epoch_changes.clone();
	let pruning_task = client.finality_notification_stream()
		.for_each(move |notification| {
			// TODO: supply is-descendent-of and maybe write to disk _now_
			// as opposed to waiting for the next epoch?
			let res = epoch_changes.lock().prune_finalized(
				descendent_query(&*client),
				&notification.hash,
				*notification.header.number(),
			);

			if let Err(e) = res {
				babe_err!("Could not prune expired epoch changes: {:?}", e);
			}

			future::ready(())
		});

	babe_info!("Starting BABE Authorship worker");
	let slot_worker = slots::start_slot_worker(
		config.0,
		select_chain,
		worker,
		sync_oracle,
		inherent_data_providers,
		babe_link.time_source,
	).map(|_| ());

	Ok(future::select(slot_worker, pruning_task).map(|_| Ok::<(), ()>(())).compat())
}

struct BabeWorker<B: BlockT, C, E, I, SO> {
	client: Arc<C>,
	block_import: Arc<Mutex<I>>,
	env: E,
	sync_oracle: SO,
	force_authoring: bool,
	keystore: KeyStorePtr,
	epoch_changes: SharedEpochChanges<B>,
	config: Config,
}

impl<B, C, E, I, Error, SO> slots::SimpleSlotWorker<B> for BabeWorker<B, C, E, I, SO> where
	B: BlockT<Hash=H256>,
	C: ProvideRuntimeApi + ProvideCache<B> + HeaderBackend<B> + HeaderMetadata<B, Error=ClientError>,
	C::Api: BabeApi<B>,
	E: Environment<B, Error=Error>,
	E::Proposer: Proposer<B, Error=Error>,
	<E::Proposer as Proposer<B>>::Create: Unpin + Send + 'static,
	I: BlockImport<B> + Send + Sync + 'static,
	SO: SyncOracle + Send + Clone,
	Error: std::error::Error + Send + From<::consensus_common::Error> + From<I::Error> + 'static,
{
	type EpochData = Epoch;
	type Claim = (BabePreDigest, AuthorityPair);
	type SyncOracle = SO;
	type Proposer = E::Proposer;
	type BlockImport = I;

	fn logging_target(&self) -> &'static str {
		"babe"
	}

	fn block_import(&self) -> Arc<Mutex<Self::BlockImport>> {
		self.block_import.clone()
	}

	fn epoch_data(&self, parent: &B::Header, slot_number: u64) -> Result<Self::EpochData, consensus_common::Error> {
		self.epoch_changes.lock().epoch_for_child_of(
			descendent_query(&*self.client),
			&parent.hash(),
			parent.number().clone(),
			slot_number,
			|slot| self.config.genesis_epoch(slot)
		)
			.map_err(|e| ConsensusError::ChainLookup(format!("{:?}", e)))?
			.map(|e| e.into_inner())
			.ok_or(consensus_common::Error::InvalidAuthoritiesSet)
	}

	fn authorities_len(&self, epoch_data: &Self::EpochData) -> usize {
		epoch_data.authorities.len()
	}

	fn claim_slot(
		&self,
		_parent_header: &B::Header,
		slot_number: SlotNumber,
		epoch_data: &Epoch,
	) -> Option<Self::Claim> {
		debug!(target: "babe", "Attempting to claim slot {}", slot_number);
		let s = authorship::claim_slot(
			slot_number,
			epoch_data,
			&*self.config,
			&self.keystore,
		);

		if let Some(_) = s {
			debug!(target: "babe", "Claimed slot {}", slot_number);
		}

		s
	}

	fn pre_digest_data(&self, _slot_number: u64, claim: &Self::Claim) -> Vec<sr_primitives::DigestItem<B::Hash>> {
		vec![
			<DigestItemFor<B> as CompatibleDigestItem>::babe_pre_digest(claim.0.clone()),
		]
	}

	fn block_import_params(&self) -> Box<dyn Fn(
		B::Header,
		&B::Hash,
		Vec<B::Extrinsic>,
		Self::Claim,
	) -> consensus_common::BlockImportParams<B> + Send> {
		Box::new(|header, header_hash, body, (_, pair)| {
			// sign the pre-sealed hash of the block and then
			// add it to a digest item.
			let signature = pair.sign(header_hash.as_ref());
			let signature_digest_item = <DigestItemFor<B> as CompatibleDigestItem>::babe_seal(signature);

			BlockImportParams {
				origin: BlockOrigin::Own,
				header,
				justification: None,
				post_digests: vec![signature_digest_item],
				body: Some(body),
				finalized: false,
				auxiliary: Vec::new(), // block-weight is written in block import.
				// TODO: block-import handles fork choice and this shouldn't even have the
				// option to specify one.
				// https://github.com/paritytech/substrate/issues/3623
				fork_choice: ForkChoiceStrategy::LongestChain,
			}
		})
	}

	fn force_authoring(&self) -> bool {
		self.force_authoring
	}

	fn sync_oracle(&mut self) -> &mut Self::SyncOracle {
		&mut self.sync_oracle
	}

	fn proposer(&mut self, block: &B::Header) -> Result<Self::Proposer, consensus_common::Error> {
		self.env.init(block).map_err(|e| {
			consensus_common::Error::ClientImport(format!("{:?}", e)).into()
		})
	}
}

impl<B, C, E, I, Error, SO> SlotWorker<B> for BabeWorker<B, C, E, I, SO> where
	B: BlockT<Hash=H256>,
	C: ProvideRuntimeApi + ProvideCache<B> + HeaderBackend<B> + HeaderMetadata<B, Error=ClientError> + Send + Sync,
	C::Api: BabeApi<B>,
	E: Environment<B, Error=Error> + Send + Sync,
	E::Proposer: Proposer<B, Error=Error>,
	<E::Proposer as Proposer<B>>::Create: Unpin + Send + 'static,
	I: BlockImport<B> + Send + Sync + 'static,
	SO: SyncOracle + Send + Sync + Clone,
	Error: std::error::Error + Send + From<::consensus_common::Error> + From<I::Error> + 'static,
{
	type OnSlot = Pin<Box<dyn Future<Output = Result<(), consensus_common::Error>> + Send>>;

	fn on_slot(&mut self, chain_head: B::Header, slot_info: SlotInfo) -> Self::OnSlot {
		<Self as slots::SimpleSlotWorker<B>>::on_slot(self, chain_head, slot_info)
	}
}

/// Extract the BABE pre digest from the given header. Pre-runtime digests are
/// mandatory, the function will return `Err` if none is found.
fn find_pre_digest<H: Header>(header: &H) -> Result<BabePreDigest, String>
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


#[derive(Default, Clone)]
struct TimeSource(Arc<Mutex<(Option<Duration>, Vec<(Instant, u64)>)>>);

impl SlotCompatible for TimeSource {
	fn extract_timestamp_and_slot(
		&self,
		data: &InherentData,
	) -> Result<(TimestampInherent, u64, std::time::Duration), consensus_common::Error> {
		trace!(target: "babe", "extract timestamp");
		data.timestamp_inherent_data()
			.and_then(|t| data.babe_inherent_data().map(|a| (t, a)))
			.map_err(Into::into)
			.map_err(consensus_common::Error::InherentData)
			.map(|(x, y)| (x, y, self.0.lock().0.take().unwrap_or_default()))
	}
}

/// State that must be shared between the import queue and the authoring logic.
#[derive(Clone)]
pub struct BabeLink<Block: BlockT> {
	time_source: TimeSource,
	epoch_changes: SharedEpochChanges<Block>,
	config: Config,
}
/// A verifier for Babe blocks.
pub struct BabeVerifier<B, E, Block: BlockT, RA, PRA> {
	client: Arc<Client<B, E, Block, RA>>,
	api: Arc<PRA>,
	inherent_data_providers: inherents::InherentDataProviders,
	config: Config,
	epoch_changes: SharedEpochChanges<Block>,
	time_source: TimeSource,
}

impl<B, E, Block: BlockT, RA, PRA> BabeVerifier<B, E, Block, RA, PRA> {
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

impl<B, E, Block, RA, PRA> Verifier<Block> for BabeVerifier<B, E, Block, RA, PRA> where
	Block: BlockT<Hash=H256>,
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
	RA: Send + Sync,
	PRA: ProvideRuntimeApi + Send + Sync + AuxStore + ProvideCache<Block>,
	PRA::Api: BlockBuilderApi<Block> + BabeApi<Block>,
{
	fn verify(
		&mut self,
		origin: BlockOrigin,
		header: Block::Header,
		justification: Option<Justification>,
		mut body: Option<Vec<Block::Extrinsic>>,
	) -> Result<(BlockImportParams<Block>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
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

		let (_, slot_now, _) = self.time_source.extract_timestamp_and_slot(&inherent_data)
			.map_err(|e| format!("Could not extract timestamp and slot: {:?}", e))?;

		let hash = header.hash();
		let parent_hash = *header.parent_hash();

		let parent_header = self.client.header(&BlockId::Hash(parent_hash))
			.map_err(|e| format!("Could not fetch parent header {:?}: {:?}", parent_hash, e))?
			.ok_or_else(|| format!("Parent header {:?} not found.", parent_hash))?;

		let pre_digest = find_pre_digest::<Block::Header>(&header)?;
		let epoch = {
			let epoch_changes = self.epoch_changes.lock();
			epoch_changes.epoch_for_child_of(
				descendent_query(&*self.client),
				&parent_hash,
				parent_header.number().clone(),
				pre_digest.slot_number(),
				|slot| self.config.genesis_epoch(slot),
			)
				.map_err(|e| format!("{:?}", e))?
				.ok_or_else(|| format!("Could not fetch epoch at {:?}", parent_hash))?
		};

		// We add one to the current slot to allow for some small drift.
		// FIXME #1019 in the future, alter this queue to allow deferring of headers
		let v_params = verification::VerificationParams {
			header: header.clone(),
			pre_digest: Some(pre_digest.clone()),
			slot_now: slot_now + 1,
			epoch: epoch.as_ref(),
			config: &self.config,
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
					&*self.api,
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

				let block_import_params = BlockImportParams {
					origin,
					header: pre_header,
					post_digests: vec![verified_info.seal],
					body,
					finalized: false,
					justification,
					auxiliary: Vec::new(),
					// TODO: block-import handles fork choice and this shouldn't even have the
					// option to specify one.
					// https://github.com/paritytech/substrate/issues/3623
					fork_choice: ForkChoiceStrategy::LongestChain,
				};

				Ok((block_import_params, Default::default()))
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

		let pre_digest = find_pre_digest::<Block::Header>(&block.header)
			.expect("valid babe headers must contain a predigest; \
					 header has been already verified; qed");
		let slot_number = pre_digest.slot_number();

		let mut epoch_changes = self.epoch_changes.lock();

		// check if there's any epoch change expected to happen at this slot.
		// `epoch` is the epoch to verify the block under, and `first_in_epoch` is true
		// if this is the first block in its chain for that epoch.
		//
		// also provides the total weight of the chain, including the imported block.
		let (epoch, first_in_epoch, parent_weight) = {
			let parent_hash = *block.header.parent_hash();
			let parent_header = self.client.header(&BlockId::Hash(parent_hash))
				.map_err(|e| ConsensusError::ChainLookup(e.to_string()))?
				.ok_or_else(|| ConsensusError::ChainLookup(babe_err!(
					"Parent ({}) of {} unavailable. Cannot import",
					parent_hash,
					hash
				)))?;

			let parent_slot = find_pre_digest::<Block::Header>(&parent_header)
				.map(|d| d.slot_number())
				.expect("parent is non-genesis; valid BABE headers contain a pre-digest; \
						 header has already been verified; qed");

			let parent_weight = if *parent_header.number() == Zero::zero() {
				0
			} else {
				aux_schema::load_block_weight(&*self.client, parent_hash)
					.map_err(|e| ConsensusError::ClientImport(e.to_string()))?
					.ok_or_else(|| ConsensusError::ClientImport(
						babe_err!("Parent block of {} has no associated weight", hash)
					))?
			};

			let epoch = epoch_changes.epoch_for_child_of(
				descendent_query(&*self.client),
				&parent_hash,
				*parent_header.number(),
				slot_number,
				|slot| self.config.genesis_epoch(slot),
			)
				.map_err(|e: fork_tree::Error<client::error::Error>| ConsensusError::ChainLookup(
					babe_err!("Could not look up epoch: {:?}", e)
				))?
				.ok_or_else(|| ConsensusError::ClientImport(
					babe_err!("Block {} is not valid under any epoch.", hash)
				))?;

			let first_in_epoch = parent_slot < epoch.as_ref().start_slot;
			(epoch, first_in_epoch, parent_weight)
		};

		let total_weight = parent_weight + pre_digest.added_weight();

		// search for this all the time so we can reject unexpected announcements.
		let next_epoch_digest = find_next_epoch_digest::<Block>(&block.header)
			.map_err(|e| ConsensusError::from(ConsensusError::ClientImport(e.to_string())))?;

		match (first_in_epoch, next_epoch_digest.is_some()) {
			(true, true) => {},
			(false, false) => {},
			(true, false) => {
				return Err(
					ConsensusError::ClientImport(
						babe_err!("Expected epoch change to happen at {:?}, s{}", hash, slot_number),
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

			babe_info!("New epoch {} launching at block {} (block slot {} >= start slot {}).",
				epoch.as_ref().epoch_index, hash, slot_number, epoch.as_ref().start_slot);
			babe_info!("Next epoch starts at slot {}", next_epoch.as_ref().start_slot);

			// track the epoch change in the fork tree
			let res = epoch_changes.import(
				descendent_query(&*self.client),
				hash,
				number,
				*block.header.parent_hash(),
				next_epoch,
			);


			if let Err(e) = res {
				let err = ConsensusError::ClientImport(format!("{:?}", e));
				babe_err!("Failed to launch next epoch: {:?}", e);
				*epoch_changes = old_epoch_changes.expect("set `Some` above and not taken; qed");
				return Err(err);
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
			let (last_best, last_best_number) = {
				let info = self.client.info().chain;
				(info.best_hash, info.best_number)
			};

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

			ForkChoiceStrategy::Custom(if total_weight > last_best_weight {
				true
			} else if total_weight == last_best_weight {
				number > last_best_number
			} else {
				false
			})
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

/// Produce a BABE block-import object to be used later on in the construction of
/// an import-queue.
///
/// Also returns a link object used to correctly instantiate the import queue
/// and background worker.
pub fn block_import<B, E, Block: BlockT<Hash=H256>, I, RA, PRA>(
	config: Config,
	wrapped_block_import: I,
	client: Arc<Client<B, E, Block, RA>>,
	api: Arc<PRA>,
) -> ClientResult<(BabeBlockImport<B, E, Block, I, RA, PRA>, BabeLink<Block>)> where
	B: Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher>,
{
	let epoch_changes = aux_schema::load_epoch_changes(&*client)?;
	let link = BabeLink {
		epoch_changes: epoch_changes.clone(),
		time_source: Default::default(),
		config: config.clone(),
	};

	let import = BabeBlockImport::new(
		client,
		api,
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
pub fn import_queue<B, E, Block: BlockT<Hash=H256>, I, RA, PRA>(
	babe_link: BabeLink<Block>,
	block_import: I,
	justification_import: Option<BoxJustificationImport<Block>>,
	finality_proof_import: Option<BoxFinalityProofImport<Block>>,
	client: Arc<Client<B, E, Block, RA>>,
	api: Arc<PRA>,
	inherent_data_providers: InherentDataProviders,
) -> ClientResult<BabeImportQueue<Block>> where
	B: Backend<Block, Blake2Hasher> + 'static,
	I: BlockImport<Block,Error=ConsensusError> + Send + Sync + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Clone + Send + Sync + 'static,
	RA: Send + Sync + 'static,
	PRA: ProvideRuntimeApi + ProvideCache<Block> + Send + Sync + AuxStore + 'static,
	PRA::Api: BlockBuilderApi<Block> + BabeApi<Block>,
{
	register_babe_inherent_data_provider(&inherent_data_providers, babe_link.config.slot_duration)?;

	let verifier = BabeVerifier {
		client: client.clone(),
		api,
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
	) -> Option<BabePreDigest> where
		B: BlockT<Hash=H256>,
		C: ProvideRuntimeApi + ProvideCache<B> + HeaderBackend<B> + HeaderMetadata<B, Error=ClientError>,
		C::Api: BabeApi<B>,
	{
		let epoch = link.epoch_changes.lock().epoch_for_child_of(
			descendent_query(client),
			&parent.hash(),
			parent.number().clone(),
			slot_number,
			|slot| link.config.genesis_epoch(slot),
		).unwrap().unwrap();

		authorship::claim_slot(
			slot_number,
			epoch.as_ref(),
			&link.config,
			keystore,
		).map(|(digest, _)| digest)
	}
}
