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

//! # Sassafras Consensus

mod aux_schema;

use std::{
	sync::Arc, time::{Duration, Instant}, collections::HashMap, convert::TryInto,
};
use log::trace;
use codec::{Encode, Decode};
use parking_lot::Mutex;
use merlin::Transcript;
use sp_core::{H256, crypto::{Pair, Public}};
use sp_blockchain::{ProvideCache, HeaderMetadata, Result as ClientResult};
use sp_inherents::InherentData;
use sp_timestamp::{TimestampInherentData, InherentType as TimestampInherent};
use sp_consensus::{
	Error as ConsensusError, BlockImportParams, BlockOrigin, ImportResult,
	BlockImport, BlockCheckParams,
};
use sp_consensus::import_queue::{Verifier, CacheKeyId, BasicQueue};
use sp_consensus_sassafras::{
	SASSAFRAS_ENGINE_ID, AuthorityPair, AuthorityId, Randomness, VRFProof,
	SassafrasAuthorityWeight, SlotNumber, SassafrasConfiguration,
	SassafrasApi,
};
use sp_consensus_sassafras::digests::{
	NextEpochDescriptor, PostBlockDescriptor, PreDigest, CompatibleDigestItem
};
use sp_consensus_sassafras::inherents::SassafrasInherentData;
use sp_runtime::Justification;
use sp_runtime::traits::{Block as BlockT, Header};
use sp_api::{ApiExt, ProvideRuntimeApi, NumberFor};
use sp_block_builder::BlockBuilder as BlockBuilderApi;
use sc_client::{Client, CallExecutor};
use sc_client_api::backend::{AuxStore, Backend};
use sc_consensus_epochs::{
	descendent_query, Epoch as EpochT, SharedEpochChanges, ViableEpochDescriptor
};
use sc_consensus_slots::SlotCompatible;

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
	#[display(fmt = "Could not extract timestamp and slot: {:?}", _0)]
	Extraction(sp_consensus::Error),
	#[display(fmt = "Header {:?} rejected: too far in the future", _0)]
	TooFarInFuture(B::Hash),
	#[display(fmt = "Parent ({}) of {} unavailable. Cannot import", _0, _1)]
	ParentUnavailable(B::Hash, B::Hash),
	#[display(fmt = "Could not fetch parent header: {:?}", _0)]
	FetchParentHeader(sp_blockchain::Error),
	InvalidEpochData,
	MultiplePreRuntimeDigest,
	NoPreRuntimeDigest,
	MultipleNextEpochDescriptor,
	MultiplePostBlockDescriptor,
	InvalidTicketVRFIndex,
	InvalidAuthorityId,
	InvalidSeal,
	HeaderUnsealed(B::Hash),
	TicketVRFVerificationFailed,
	PostVRFVerificationFailed,
	SlotInPast,
	SlotInFuture,
	Runtime(sp_inherents::Error),
	Client(sp_blockchain::Error),
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

/// Configuration for Sassafras.
#[derive(Clone)]
pub struct Config(sc_consensus_slots::SlotDuration<SassafrasConfiguration>);

impl Config {
	/// Either fetch the slot duration from disk or compute it from the genesis
	/// state.
	pub fn get_or_compute<B: BlockT, C>(client: &C) -> ClientResult<Self> where
		C: AuxStore + ProvideRuntimeApi<B>, C::Api: SassafrasApi<B, Error = sp_blockchain::Error>,
	{
		sc_consensus_slots::SlotDuration::get_or_compute(client, |a, b| a.configuration(b)).map(Self)
	}

	/// Create the genesis epoch (epoch #0)
	pub fn genesis_epoch(&self, slot_number: SlotNumber) -> Epoch {
		let proofs = self.genesis_proofs.clone()
			.into_iter()
			.map(|p| p.try_into().expect("Genesis proofs are invalid"))
			.collect::<Vec<VRFProof>>();

		Epoch {
			epoch_index: 0,
			start_slot: slot_number,
			duration: self.epoch_length,

			validating: ValidatorSet {
				proofs: proofs.clone(),
				authorities: self.genesis_authorities.clone(),
				randomness: self.randomness.clone(),
			},
			publishing: ValidatorSet {
				proofs,
				authorities: self.genesis_authorities.clone(),
				randomness: self.randomness.clone(),
			},
		}
	}
}

impl std::ops::Deref for Config {
	type Target = SassafrasConfiguration;

	fn deref(&self) -> &SassafrasConfiguration {
		&*self.0
	}
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

pub struct SassafrasVerifier<B, E, Block: BlockT, RA, PRA> {
	client: Arc<Client<B, E, Block, RA>>,
	api: Arc<PRA>,
	inherent_data_providers: sp_inherents::InherentDataProviders,
	link: SassafrasLink<Block>,
}

impl<B, E, Block: BlockT, RA, PRA> BabeVerifier<B, E, Block, RA, PRA> {
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

impl<B, E, Block, RA, PRA> SassafrasVerifier<B, E, Block, RA, PRA> where
	Block: BlockT<Hash=H256>,
	B: Backend<Block> + 'static,
	E: CallExecutor<Block> + 'static + Clone + Send + Sync,
	RA: Send + Sync,
	PRA: ProvideRuntimeApi<Block> + Send + Sync + AuxStore + ProvideCache<Block>,
	PRA::Api: BlockBuilderApi<Block, Error = sp_blockchain::Error> + SassafrasApi<Block, Error = sp_blockchain::Error>,
{
	fn verify(
		&mut self,
		origin: BlockOrigin,
		header: Block::Header,
		justification: Option<Justification>,
		mut body: Option<Vec<Block::Extrinsic>>,
	) -> Result<(BlockImportParams<Block, ()>, Option<Vec<(CacheKeyId, Vec<u8>)>>), Error<Block>> {
		trace!(
			target: "sassafras",
			"Verifying origin: {:?} header: {:?} justification: {:?} body: {:?}",
			origin,
			header,
			justification,
			body,
		);

		let mut inherent_data = self
			.inherent_data_providers
			.create_inherent_data()
			.map_err(Error::Runtime)?;

		let (_, slot_now, _) = self.time_source.extract_timestamp_and_slot(&inherent_data)
			.map_err(Error::Extraction)?;

		let hash = header.hash();
		let parent_hash = *header.parent_hash();

		let parent_header_metadata = self.client.header_metadata(parent_hash)
			.map_err(Error::FetchParentHeader)?;

		// First, Verify pre-runtime digest.
		let pre_digest = find_pre_digest::<Block>(&header)?;
		let mut epoch_changes = self.epoch_changes.lock();
		let epoch_descriptor = epoch_changes.epoch_descriptor_for_child_of(
			descendent_query(&*self.client),
			&parent_hash,
			parent_header_metadata.number,
			pre_digest.slot_number(),
		)
			.map_err(|e| Error::ForkTree(Box::new(e)))?
			.ok_or_else(|| Error::FetchEpoch(parent_hash))?;
		let viable_epoch = epoch_changes.viable_epoch_mut(
			&epoch_descriptor,
			|slot| self.link.config.genesis_epoch(slot),
		).ok_or_else(|| Error::FetchEpoch(parent_hash))?;

		let v_params = verification::VerificationParams {
			header: header.clone(),
			pre_digest: Some(pre_digest.clone()),
			slot_now: slot_now + 1,
			epoch: viable_epoch.as_ref(),
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

				let mut intermediates = HashMap::new();
				intermediates.insert(
					Cow::from(INTERMEDIATE_KEY),
					Box::new(BabeIntermediate::<Block> {
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
				debug!(target: "babe", "Checking {:?} failed; {:?}, {:?}.", hash, a, b);
				telemetry!(CONSENSUS_DEBUG; "babe.header_too_far_in_future";
					"hash" => ?hash, "a" => ?a, "b" => ?b
				);
				Err(Error::<Block>::TooFarInFuture(hash).into())
			}
		}

		Ok((block_import_params, Default::default()))
	}
}

impl<B, E, Block, RA, PRA> Verifier<Block> for SassafrasVerifier<B, E, Block, RA, PRA> where
	Block: BlockT<Hash=H256>,
	B: Backend<Block> + 'static,
	E: CallExecutor<Block> + 'static + Clone + Send + Sync,
	RA: Send + Sync,
	PRA: ProvideRuntimeApi<Block> + Send + Sync + AuxStore + ProvideCache<Block>,
	PRA::Api: BlockBuilderApi<Block, Error = sp_blockchain::Error>,
{
	fn verify(
		&mut self,
		origin: BlockOrigin,
		mut header: Block::Header,
		justification: Option<Justification>,
		mut body: Option<Vec<Block::Extrinsic>>,
	) -> Result<(BlockImportParams<Block, ()>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
		self.verify(origin, header, justification, body).map_err(Into::into)
	}
}

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

pub struct SassafrasBlockImport<B, E, Block: BlockT, I, RA, PRA> {
	inner: I,
	client: Arc<Client<B, E, Block, RA>>,
	api: Arc<PRA>,
	link:
}

impl<B, E, Block: BlockT, I, RA, PRA> BlockImport<Block> for
	SassafrasBlockImport<B, E, Block, I, RA, PRA>
where
	I: BlockImport<Block, Transaction = sp_api::TransactionFor<PRA, Block>> + Send + Sync,
	I::Error: Into<ConsensusError>,
	B: Backend<Block> + 'static,
	E: CallExecutor<Block> + 'static + Clone + Send + Sync,
	Client<B, E, Block, RA>: AuxStore,
	RA: Send + Sync,
	PRA: ProvideRuntimeApi<Block> + ProvideCache<Block>,
	PRA::Api: ApiExt<Block, StateBackend = B::State>,
{
	type Error = ConsensusError;
	type Transaction = sp_api::TransactionFor<PRA, Block>;

	fn import_block(
		&mut self,
		mut block: BlockImportParams<Block, Self::Transaction>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		let hash = block.post_header().hash();
		let parent_hash = *block.header.parent_hash();
		let number = block.header.number().clone();

		// let pre_digest = find_pre_digest::<Block>(&block.header)?;
		// TODO: Verify that the slot is increasing, and not in the future.

		let import_result = self.inner.import_block(block, new_cache);

		import_result.map_err(Into::into)
	}

	fn check_block(
		&mut self,
		block: BlockCheckParams<Block>,
	) -> Result<ImportResult, Self::Error> {
		self.inner.check_block(block).map_err(Into::into)
	}
}

fn find_pre_digest<B: BlockT>(
	header: &B::Header,
) -> Result<PreDigest, Error<B>> {
	let mut pre_digest = None;
	for log in header.digest().logs() {
		match (log.as_sassafras_pre_digest(), pre_digest.is_some()) {
			(Some(_), true) => return Err(Error::MultiplePreRuntimeDigest),
			(None, _) => (),
			(s, false) => pre_digest = s,
		}
	}
	pre_digest.ok_or_else(|| Error::NoPreRuntimeDigest)
}

fn find_post_block_descriptor<B: BlockT>(
	header: &B::Header,
) -> Result<Option<PostBlockDescriptor>, Error<B>> {
	let mut desc = None;
	for log in header.digest().logs() {
		match (log.as_sassafras_post_block_descriptor(), desc.is_some()) {
			(Some(_), true) => return Err(Error::MultiplePostBlockDescriptor),
			(None, _) => (),
			(s, false) => desc = s,
		}
	}
	Ok(desc)
}

fn find_next_epoch_descriptor<B: BlockT>(
	header: &B::Header,
) -> Result<Option<NextEpochDescriptor>, Error<B>> {
	let mut desc = None;
	for log in header.digest().logs() {
		match (log.as_sassafras_next_epoch_descriptor(), desc.is_some()) {
			(Some(_), true) => return Err(Error::MultipleNextEpochDescriptor),
			(None, _) => (),
			(s, false) => desc = s,
		}
	}
	Ok(desc)
}

fn make_ticket_transcript(
	randomness: &[u8],
	slot_number: u64,
	epoch: u64,
) -> Transcript {
	let mut transcript = Transcript::new(&SASSAFRAS_ENGINE_ID);
	transcript.append_message(b"type", b"ticket");
	transcript.append_message(b"slot number", &slot_number.to_le_bytes());
	transcript.append_message(b"current epoch", &epoch.to_le_bytes());
	transcript.append_message(b"chain randomness", randomness);
	transcript
}

fn make_post_transcript(
	randomness: &[u8],
	slot_number: u64,
	epoch: u64,
) -> Transcript {
	let mut transcript = Transcript::new(&SASSAFRAS_ENGINE_ID);
	transcript.append_message(b"type", b"post");
	transcript.append_message(b"slot number", &slot_number.to_le_bytes());
	transcript.append_message(b"current epoch", &epoch.to_le_bytes());
	transcript.append_message(b"chain randomness", randomness);
	transcript
}
