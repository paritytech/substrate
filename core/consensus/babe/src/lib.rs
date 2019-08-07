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

//! # BABE consensus
//!
//! BABE (Blind Assignment for Blockchain Extension) consensus in Substrate.

#![forbid(unsafe_code, missing_docs)]
pub use babe_primitives::*;
pub use consensus_common::SyncOracle;
use std::{collections::HashMap, sync::Arc, u64, fmt::{Debug, Display}, pin::Pin, time::{Instant, Duration}};
use babe_primitives;
use consensus_common::ImportResult;
use consensus_common::import_queue::{
	BoxJustificationImport, BoxFinalityProofImport,
};
use consensus_common::well_known_cache_keys::Id as CacheKeyId;
use sr_primitives::{generic, generic::{BlockId, OpaqueDigestItemId}, Justification};
use sr_primitives::traits::{
	Block as BlockT, Header, DigestItemFor, NumberFor, ProvideRuntimeApi,
	SimpleBitOps, Zero,
};
use keystore::KeyStorePtr;
use runtime_support::serde::{Serialize, Deserialize};
use codec::{Decode, Encode};
use parking_lot::{Mutex, MutexGuard};
use primitives::{Blake2Hasher, H256, Pair, Public};
use merlin::Transcript;
use inherents::{InherentDataProviders, InherentData};
use substrate_telemetry::{
	telemetry,
	CONSENSUS_TRACE,
	CONSENSUS_DEBUG,
	CONSENSUS_WARN,
	CONSENSUS_INFO,
};
use schnorrkel::{
	keys::Keypair,
	vrf::{
		VRFProof, VRFProofBatchable, VRFInOut,
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
use consensus_common::{SelectChain, well_known_cache_keys};
use consensus_common::import_queue::{Verifier, BasicQueue};
use client::{
	block_builder::api::BlockBuilder as BlockBuilderApi,
	blockchain::{self, HeaderBackend, ProvideCache}, BlockchainEvents, CallExecutor, Client,
	runtime_api::ApiExt, error::Result as ClientResult, backend::{AuxStore, Backend},
	ProvideUncles,
	utils::is_descendent_of,
};
use transaction_pool::txpool::{SubmitExtrinsic, ChainApi};
use fork_tree::ForkTree;
use slots::{CheckedHeader, check_equivocation};
use futures::{prelude::*, future};
use futures01::Stream as _;
use futures_timer::Delay;
use log::{error, warn, debug, info, trace};
use consensus_common_primitives::AuthorshipEquivocationProof;

use slots::{SlotWorker, SlotData, SlotInfo, SlotCompatible, SignedDuration};

mod aux_schema;
#[cfg(test)]
mod tests;
pub use babe_primitives::{AuthorityId, AuthorityPair, AuthoritySignature, BabeEquivocationProof};

/// A slot duration. Create with `get_or_compute`.
// FIXME: Once Rust has higher-kinded types, the duplication between this
// and `super::babe::Config` can be eliminated.
// https://github.com/paritytech/substrate/issues/2434
pub struct Config(slots::SlotDuration<BabeConfiguration>);

impl Config {
	/// Either fetch the slot duration from disk or compute it from the genesis
	/// state.
	pub fn get_or_compute<B: BlockT, C>(client: &C) -> ClientResult<Self>
	where
		C: AuxStore + ProvideRuntimeApi, C::Api: BabeApi<B>,
	{
		trace!(target: "babe", "Getting slot duration");
		match slots::SlotDuration::get_or_compute(client, |a, b| a.startup_data(b)).map(Self) {
			Ok(s) => Ok(s),
			Err(s) => {
				warn!(target: "babe", "Failed to get slot duration");
				Err(s)
			}
		}
	}

	/// Get the slot duration in milliseconds.
	pub fn get(&self) -> u64 {
		self.0.slot_duration
	}

	/// Retrieve the threshold calculation constant `c`.
	pub fn c(&self) -> (u64, u64) {
		self.0.c
	}
}

impl SlotCompatible for BabeLink {
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

/// Parameters for BABE.
pub struct BabeParams<C, E, I, SO, SC> {
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
	pub time_source: BabeLink,
}

/// Start the babe worker. The returned future should be run in a tokio runtime.
pub fn start_babe<B, C, SC, E, I, SO, Error, H>(BabeParams {
	config,
	client,
	keystore,
	select_chain,
	block_import,
	env,
	sync_oracle,
	inherent_data_providers,
	force_authoring,
	time_source,
}: BabeParams<C, E, I, SO, SC>) -> Result<
	impl futures01::Future<Item=(), Error=()>,
	consensus_common::Error,
> where
	B: BlockT<Header=H>,
	C: ProvideRuntimeApi + ProvideCache<B> + ProvideUncles<B> + Send + Sync + 'static,
	C::Api: BabeApi<B>,
	SC: SelectChain<B> + 'static,
	E::Proposer: Proposer<B, Error=Error>,
	<E::Proposer as Proposer<B>>::Create: Unpin + Send + 'static,
	H: Header<Hash=B::Hash>,
	E: Environment<B, Error=Error>,
	I: BlockImport<B> + Send + Sync + 'static,
	Error: std::error::Error + Send + From<::consensus_common::Error> + From<I::Error> + 'static,
	SO: SyncOracle + Send + Sync + Clone,
{
	let worker = BabeWorker {
		client: client.clone(),
		block_import: Arc::new(Mutex::new(block_import)),
		env,
		sync_oracle: sync_oracle.clone(),
		force_authoring,
		c: config.c(),
		keystore,
	};
	register_babe_inherent_data_provider(&inherent_data_providers, config.0.slot_duration())?;
	uncles::register_uncles_inherent_data_provider(
		client.clone(),
		select_chain.clone(),
		&inherent_data_providers,
	)?;
	Ok(slots::start_slot_worker(
		config.0,
		select_chain,
		worker,
		sync_oracle,
		inherent_data_providers,
		time_source,
	).map(|()| Ok::<(), ()>(())).compat())
}

struct BabeWorker<C, E, I, SO> {
	client: Arc<C>,
	block_import: Arc<Mutex<I>>,
	env: E,
	sync_oracle: SO,
	force_authoring: bool,
	c: (u64, u64),
	keystore: KeyStorePtr,
}

impl<Hash, H, B, C, E, I, Error, SO> SlotWorker<B> for BabeWorker<C, E, I, SO> where
	B: BlockT<Header=H, Hash=Hash>,
	C: ProvideRuntimeApi + ProvideCache<B>,
	C::Api: BabeApi<B>,
	E: Environment<B, Error=Error>,
	E::Proposer: Proposer<B, Error=Error>,
	<E::Proposer as Proposer<B>>::Create: Unpin + Send + 'static,
	Hash: Debug + Eq + Copy + SimpleBitOps + Encode + Decode + Serialize +
		for<'de> Deserialize<'de> + Debug + Default + AsRef<[u8]> + AsMut<[u8]> +
		std::hash::Hash + Display + Send + Sync + 'static,
	H: Header<Hash=B::Hash>,
	I: BlockImport<B> + Send + Sync + 'static,
	SO: SyncOracle + Send + Clone,
	Error: std::error::Error + Send + From<::consensus_common::Error> + From<I::Error> + 'static,
{
	type OnSlot = Pin<Box<dyn Future<Output = Result<(), consensus_common::Error>> + Send>>;

	fn on_slot(
		&mut self,
		chain_head: B::Header,
		slot_info: SlotInfo,
	) -> Self::OnSlot {
		let ref client = self.client;
		let block_import = self.block_import.clone();

		let (timestamp, slot_number, slot_duration) =
			(slot_info.timestamp, slot_info.number, slot_info.duration);

		let epoch = match epoch(client.as_ref(), &BlockId::Hash(chain_head.hash())) {
			Ok(authorities) => authorities,
			Err(e) => {
				error!(
					target: "babe",
					"Unable to fetch authorities at block {:?}: {:?}",
					chain_head.hash(),
					e
				);
				telemetry!(CONSENSUS_WARN; "babe.unable_fetching_authorities";
					"slot" => ?chain_head.hash(), "err" => ?e
				);
				return Box::pin(future::ready(Ok(())));
			}
		};

		let Epoch { ref authorities, .. } = epoch;

		if authorities.is_empty() {
			error!(target: "babe", "No authorities at block {:?}", chain_head.hash());
		}

		if !self.force_authoring && self.sync_oracle.is_offline() && authorities.len() > 1 {
			debug!(target: "babe", "Skipping proposal slot. Waiting for the network.");
			telemetry!(CONSENSUS_DEBUG; "babe.skipping_proposal_slot";
				"authorities_len" => authorities.len()
			);
			return Box::pin(future::ready(Ok(())));
		}

		let proposal_work = if let Some(claim) = claim_slot(
			slot_info.number,
			epoch,
			self.c,
			&self.keystore,
		) {
			let ((inout, vrf_proof, _batchable_proof), authority_index, key) = claim;

			debug!(
				target: "babe", "Starting authorship at slot {}; timestamp = {}",
				slot_number,
				timestamp,
			);
			telemetry!(CONSENSUS_DEBUG; "babe.starting_authorship";
				"slot_number" => slot_number, "timestamp" => timestamp
			);

			// we are the slot author. make a block and sign it.
			let mut proposer = match self.env.init(&chain_head) {
				Ok(p) => p,
				Err(e) => {
					warn!(target: "babe",
						"Unable to author block in slot {:?}: {:?}",
						slot_number,
						e,
					);
					telemetry!(CONSENSUS_WARN; "babe.unable_authoring_block";
						"slot" => slot_number, "err" => ?e
					);
					return Box::pin(future::ready(Ok(())))
				}
			};

			let inherent_digest = BabePreDigest {
				vrf_proof,
				vrf_output: inout.to_output(),
				authority_index: authority_index as u32,
				slot_number,
			};

			// deadline our production to approx. the end of the slot
			let remaining_duration = slot_info.remaining_duration();
			futures::future::select(
				proposer.propose(
					slot_info.inherent_data,
					generic::Digest {
						logs: vec![
							generic::DigestItem::babe_pre_digest(inherent_digest.clone()),
						],
					},
					remaining_duration,
				).map_err(|e| consensus_common::Error::ClientImport(format!("{:?}", e)).into()),
				Delay::new(remaining_duration)
					.map_err(|err| consensus_common::Error::FaultyTimer(err).into())
			).map(|v| match v {
				futures::future::Either::Left((v, _)) => v.map(|v| (v, key)),
				futures::future::Either::Right((Ok(_), _)) =>
					Err(consensus_common::Error::ClientImport("Timeout in the BaBe proposer".into())),
				futures::future::Either::Right((Err(err), _)) => Err(err),
			})
		} else {
			return Box::pin(future::ready(Ok(())));
		};

		Box::pin(proposal_work.map_ok(move |(b, key)| {
			// minor hack since we don't have access to the timestamp
			// that is actually set by the proposer.
			let slot_after_building = SignedDuration::default().slot_now(slot_duration);
			if slot_after_building != slot_number {
				info!(
					target: "babe",
					"Discarding proposal for slot {}; block production took too long",
					slot_number
				);
				telemetry!(CONSENSUS_INFO; "babe.discarding_proposal_took_too_long";
					"slot" => slot_number
				);
				return;
			}

			let (header, body) = b.deconstruct();
			let header_num = header.number().clone();
			let parent_hash = header.parent_hash().clone();

			// sign the pre-sealed hash of the block and then
			// add it to a digest item.
			let header_hash = header.hash();
			let signature = key.sign(header_hash.as_ref());
			let signature_digest_item = DigestItemFor::<B>::babe_seal(signature);

			let import_block = BlockImportParams::<B> {
				origin: BlockOrigin::Own,
				header,
				justification: None,
				post_digests: vec![signature_digest_item],
				body: Some(body),
				finalized: false,
				auxiliary: Vec::new(),
				fork_choice: ForkChoiceStrategy::LongestChain,
			};

			info!(target: "babe",
					"Pre-sealed block for proposal at {}. Hash now {:?}, previously {:?}.",
					header_num,
					import_block.post_header().hash(),
					header_hash,
			);

			telemetry!(CONSENSUS_INFO; "babe.pre_sealed_block";
				"header_num" => ?header_num,
				"hash_now" => ?import_block.post_header().hash(),
				"hash_previously" => ?header_hash,
			);

			if let Err(e) = block_import.lock().import_block(import_block, Default::default()) {
				warn!(target: "babe", "Error with block built on {:?}: {:?}",
						parent_hash, e);
				telemetry!(CONSENSUS_WARN; "babe.err_with_block_built_on";
					"hash" => ?parent_hash, "err" => ?e
				);
			}
		}))
	}
}

macro_rules! babe_err {
	($($i: expr),+) => {
		{ debug!(target: "babe", $($i),+)
		; format!($($i),+)
		}
	};
}

/// Extract the BABE epoch change digest from the given header, if it exists.
fn find_next_epoch_digest<B: BlockT>(header: &B::Header) -> Result<Option<Epoch>, String>
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

/// Check a header has been signed by the right key. If the slot is too far in
/// the future, an error will be returned. If successful, returns the pre-header
/// and the digest item containing the seal.
///
/// The seal must be the last digest.  Otherwise, the whole header is considered
/// unsigned.  This is required for security and must not be changed.
///
/// This digest item will always return `Some` when used with `as_babe_pre_digest`.
// FIXME #1018 needs misbehavior types. The `transaction_pool` parameter will be 
// used to submit such misbehavior reports.
fn check_header<B: BlockT + Sized, C: AuxStore, T>(
	client: &C,
	slot_now: u64,
	mut header: B::Header,
	hash: B::Hash,
	authorities: &[(AuthorityId, BabeWeight)],
	randomness: [u8; 32],
	epoch_index: u64,
	c: (u64, u64),
	transaction_pool: Option<&T>,
) -> Result<CheckedHeader<B::Header, (DigestItemFor<B>, DigestItemFor<B>)>, String> where
	DigestItemFor<B>: CompatibleDigestItem,
	C: ProvideRuntimeApi + HeaderBackend<B>,
	C::Api: BabeApi<B>,
	T: SubmitExtrinsic + Send + Sync + 'static,
	<T as SubmitExtrinsic>::Api: ChainApi<Block=B>,
{
	trace!(target: "babe", "Checking header");
	let seal = match header.digest_mut().pop() {
		Some(x) => x,
		None => return Err(babe_err!("Header {:?} is unsealed", hash)),
	};

	let sig = seal.as_babe_seal().ok_or_else(|| {
		babe_err!("Header {:?} has a bad seal", hash)
	})?;

	let pre_digest = find_pre_digest::<B::Header, BabePreDigest>(&header)?;

	let BabePreDigest { slot_number, authority_index, ref vrf_proof, ref vrf_output } = pre_digest;

	if slot_number > slot_now {
		header.digest_mut().push(seal);
		Ok(CheckedHeader::Deferred(header, slot_number))
	} else if authority_index > authorities.len() as u32 {
		Err(babe_err!("Slot author not found"))
	} else {
		let (pre_hash, author) = (header.hash(), &authorities[authority_index as usize].0);

		if AuthorityPair::verify(&sig, pre_hash, &author) {
			let (inout, _batchable_proof) = {
				let transcript = make_transcript(
					&randomness,
					slot_number,
					epoch_index,
				);

				schnorrkel::PublicKey::from_bytes(author.as_slice()).and_then(|p| {
					p.vrf_verify(transcript, vrf_output, vrf_proof)
				}).map_err(|s| {
					babe_err!("VRF verification failed: {:?}", s)
				})?
			};

			let threshold = calculate_threshold(c, authorities, authority_index as usize);
			if !check(&inout, threshold) {
				return Err(babe_err!("VRF verification of block by author {:?} failed: \
									  threshold {} exceeded", author, threshold));
			}

			if let Some(equivocation_proof) = check_equivocation::<
				_, _, BabeEquivocationProof<B::Header>, _
			>(
				client,
				slot_now,
				slot_number,
				&header,
				sig,
				author,
			).map_err(|e| e.to_string())? {
				info!(
					"Slot author {:?} is equivocating at slot {} with headers {:?} and {:?}",
					author,
					slot_number,
					equivocation_proof.first_header().hash(),
					equivocation_proof.second_header().hash(),
				);

				// Submit a transaction reporting the equivocation.
				let block_id = BlockId::number(client.info().best_number);
				
				let maybe_report_call = client
					.runtime_api()
					.construct_equivocation_transaction(&block_id, equivocation_proof);
				if let Ok(Some(report_call)) = maybe_report_call {
						transaction_pool.as_ref().map(|txpool| {
							let uxt = Decode::decode(&mut report_call.as_slice())
								.expect("Encoded extrinsic is valid; qed");
							txpool.submit_one(&block_id, uxt)
						});
						info!(target: "afg", "Equivocation report has been submitted")
				} else {
					error!(target: "afg", "Error constructing equivocation report")
				}
			}

			let pre_digest = CompatibleDigestItem::babe_pre_digest(pre_digest);
			Ok(CheckedHeader::Checked(header, (pre_digest, seal)))
		} else {
			Err(babe_err!("Bad signature on {:?}", hash))
		}
	}
}

/// State that must be shared between the import queue and the authoring logic.
#[derive(Default, Clone, Debug)]
pub struct BabeLink(Arc<Mutex<(Option<Duration>, Vec<(Instant, u64)>)>>);

/// A verifier for Babe blocks.
pub struct BabeVerifier<C, T> {
	api: Arc<C>,
	inherent_data_providers: inherents::InherentDataProviders,
	config: Config,
	time_source: BabeLink,
	transaction_pool: Option<Arc<T>>,
}

impl<C, T> BabeVerifier<C, T> {
	fn check_inherents<B: BlockT>(
		&self,
		block: B,
		block_id: BlockId<B>,
		inherent_data: InherentData,
	) -> Result<(), String>
		where C: ProvideRuntimeApi, C::Api: BlockBuilderApi<B>
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

impl<B: BlockT, C, T> Verifier<B> for BabeVerifier<C, T> where
	C: ProvideRuntimeApi + HeaderBackend<B> + Send + Sync + AuxStore + ProvideCache<B>,
	C::Api: BlockBuilderApi<B> + BabeApi<B>,
	T: SubmitExtrinsic + Send + Sync + 'static,
	<T as SubmitExtrinsic>::Api: ChainApi<Block=B>,
{
	fn verify(
		&mut self,
		origin: BlockOrigin,
		header: B::Header,
		justification: Option<Justification>,
		mut body: Option<Vec<B::Extrinsic>>,
	) -> Result<(BlockImportParams<B>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
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
		let Epoch { authorities, randomness, epoch_index, .. } =
			epoch(self.api.as_ref(), &BlockId::Hash(parent_hash))
				.map_err(|e| format!("Could not fetch epoch at {:?}: {:?}", parent_hash, e))?;

		// We add one to allow for some small drift.
		// FIXME #1019 in the future, alter this queue to allow deferring of headers
		let checked_header = check_header::<B, C, T>(
			&self.api,
			slot_now + 1,
			header,
			hash,
			&authorities,
			randomness,
			epoch_index,
			self.config.c(),
			self.transaction_pool.as_ref().map(|x| &**x),
		)?;

		match checked_header {
			CheckedHeader::Checked(pre_header, (pre_digest, seal)) => {
				let BabePreDigest { slot_number, .. } = pre_digest.as_babe_pre_digest()
					.expect("check_header always returns a pre-digest digest item; qed");

				// if the body is passed through, we need to use the runtime
				// to check that the internally-set timestamp in the inherents
				// actually matches the slot set in the seal.
				if let Some(inner_body) = body.take() {
					inherent_data.babe_replace_inherent_data(slot_number);
					let block = B::new(pre_header.clone(), inner_body);

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

				let import_block = BlockImportParams {
					origin,
					header: pre_header,
					post_digests: vec![seal],
					body,
					finalized: false,
					justification,
					auxiliary: Vec::new(),
					fork_choice: ForkChoiceStrategy::LongestChain,
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

/// Extract current epoch data from cache and fallback to querying the runtime
/// if the cache isn't populated.
fn epoch<B, C>(client: &C, at: &BlockId<B>) -> Result<Epoch, ConsensusError> where
	B: BlockT,
	C: ProvideRuntimeApi + ProvideCache<B>,
	C::Api: BabeApi<B>,
{
	client
		.cache()
		.and_then(|cache| cache.get_at(&well_known_cache_keys::EPOCH, at)
			.and_then(|v| Decode::decode(&mut &v[..]).ok()))
		.or_else(|| {
			if client.runtime_api().has_api::<dyn BabeApi<B>>(at).unwrap_or(false) {
				let s = BabeApi::epoch(&*client.runtime_api(), at).ok()?;
				if s.authorities.is_empty() {
					error!("No authorities!");
					None
				} else {
					Some(s)
				}
			} else {
				error!("bad api!");
				None
			}
		}).ok_or(consensus_common::Error::InvalidAuthoritiesSet)
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

fn check(inout: &VRFInOut, threshold: u128) -> bool {
	u128::from_le_bytes(inout.make_bytes::<[u8; 16]>(BABE_VRF_PREFIX)) < threshold
}

fn calculate_threshold(
	c: (u64, u64),
	authorities: &[(AuthorityId, BabeWeight)],
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

/// Claim a slot if it is our turn.  Returns `None` if it is not our turn.
///
/// This hashes the slot number, epoch, genesis hash, and chain randomness into
/// the VRF.  If the VRF produces a value less than `threshold`, it is our turn,
/// so it returns `Some(_)`.  Otherwise, it returns `None`.
fn claim_slot(
	slot_number: u64,
	Epoch { ref authorities, ref randomness, epoch_index, .. }: Epoch,
	c: (u64, u64),
	keystore: &KeyStorePtr,
) -> Option<((VRFInOut, VRFProof, VRFProofBatchable), usize, AuthorityPair)> {
	let keystore = keystore.read();
	let (key_pair, authority_index) = authorities.iter()
		.enumerate()
		.find_map(|(i, a)| {
			keystore.key_pair::<AuthorityPair>(&a.0).ok().map(|kp| (kp, i))
		})?;
	let transcript = make_transcript(randomness, slot_number, epoch_index);

	// Compute the threshold we will use.
	//
	// We already checked that authorities contains `key.public()`, so it can't
	// be empty.  Therefore, this division in `calculate_threshold` is safe.
	let threshold = calculate_threshold(c, authorities, authority_index);

	get_keypair(&key_pair)
		.vrf_sign_after_check(transcript, |inout| check(inout, threshold))
		.map(|s|(s, authority_index, key_pair))
}

fn initialize_authorities_cache<B, C>(client: &C) -> Result<(), ConsensusError> where
	B: BlockT,
	C: ProvideRuntimeApi + ProvideCache<B>,
	C::Api: BabeApi<B>,
{
	// no cache => no initialization
	let cache = match client.cache() {
		Some(cache) => cache,
		None => return Ok(()),
	};

	// check if we already have initialized the cache
	let genesis_id = BlockId::Number(Zero::zero());
	let genesis_epoch: Option<Epoch> = cache
		.get_at(&well_known_cache_keys::EPOCH, &genesis_id)
		.and_then(|v| Decode::decode(&mut &v[..]).ok());
	if genesis_epoch.is_some() {
		return Ok(());
	}

	let map_err = |error| consensus_common::Error::from(consensus_common::Error::ClientImport(
		format!(
			"Error initializing authorities cache: {}",
			error,
		)));

	let genesis_epoch = epoch(client, &genesis_id)?;
	cache.initialize(&well_known_cache_keys::EPOCH, genesis_epoch.encode())
		.map_err(map_err)
}

/// Tree of all epoch changes across all *seen* forks. Data stored in tree is
/// the hash and block number of the block signaling the epoch change, and the
/// epoch that was signalled at that block.
type EpochChanges<Block> = ForkTree<
	<Block as BlockT>::Hash,
	NumberFor<Block>,
	Epoch,
>;

/// A shared epoch changes tree.
#[derive(Clone)]
struct SharedEpochChanges<Block: BlockT> {
	inner: Arc<Mutex<EpochChanges<Block>>>,
}

impl<Block: BlockT> SharedEpochChanges<Block> {
	fn new() -> Self {
		SharedEpochChanges {
			inner: Arc::new(Mutex::new(EpochChanges::<Block>::new()))
		}
	}

	fn lock(&self) -> MutexGuard<EpochChanges<Block>> {
		self.inner.lock()
	}
}

impl<Block: BlockT> From<EpochChanges<Block>> for SharedEpochChanges<Block> {
	fn from(epoch_changes: EpochChanges<Block>) -> Self {
		SharedEpochChanges {
			inner: Arc::new(Mutex::new(epoch_changes))
		}
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
}

impl<B, E, Block: BlockT, I: Clone, RA, PRA> Clone for BabeBlockImport<B, E, Block, I, RA, PRA> {
	fn clone(&self) -> Self {
		BabeBlockImport {
			inner: self.inner.clone(),
			client: self.client.clone(),
			api: self.api.clone(),
			epoch_changes: self.epoch_changes.clone(),
		}
	}
}

impl<B, E, Block: BlockT, I, RA, PRA> BabeBlockImport<B, E, Block, I, RA, PRA> {
	fn new(
		client: Arc<Client<B, E, Block, RA>>,
		api: Arc<PRA>,
		epoch_changes: SharedEpochChanges<Block>,
		block_import: I,
	) -> Self {
		BabeBlockImport {
			client,
			api,
			inner: block_import,
			epoch_changes,
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
		mut new_cache: HashMap<well_known_cache_keys::Id, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		let hash = block.post_header().hash();
		let number = block.header.number().clone();

		// early exit if block already in chain, otherwise the check for
		// epoch changes will error when trying to re-import an epoch change
		#[allow(deprecated)]
		match self.client.backend().blockchain().status(BlockId::Hash(hash)) {
			Ok(blockchain::BlockStatus::InChain) => return Ok(ImportResult::AlreadyInChain),
			Ok(blockchain::BlockStatus::Unknown) => {},
			Err(e) => return Err(ConsensusError::ClientImport(e.to_string()).into()),
		}

		let slot_number = {
			let pre_digest = find_pre_digest::<Block::Header, BabePreDigest>(&block.header)
				.expect("valid babe headers must contain a predigest; \
						 header has been already verified; qed");
			let BabePreDigest { slot_number, .. } = pre_digest;
			slot_number
		};

		// returns a function for checking whether a block is a descendent of another
		// consistent with querying client directly after importing the block.
		let parent_hash = *block.header.parent_hash();
		let is_descendent_of = is_descendent_of(&self.client, Some((&hash, &parent_hash)));

		// check if there's any epoch change expected to happen at this slot
		let mut epoch_changes = self.epoch_changes.lock();
		let enacted_epoch = epoch_changes.find_node_where(
			&hash,
			&number,
			&is_descendent_of,
			&|epoch| epoch.start_slot <= slot_number,
		).map_err(|e| ConsensusError::from(ConsensusError::ClientImport(e.to_string())))?;

		let check_roots = || -> Result<bool, ConsensusError> {
			// this can only happen when the chain starts, since there's no
			// epoch change at genesis. afterwards every time we expect an epoch
			// change it means we will import another one.
			for (root, _, _) in epoch_changes.roots() {
				let is_descendent_of = is_descendent_of(root, &hash)
					.map_err(|e| {
						ConsensusError::from(ConsensusError::ClientImport(e.to_string()))
					})?;

				if is_descendent_of {
					return Ok(false);
				}
			}

			Ok(true)
		};

		let expected_epoch_change = enacted_epoch.is_some();
		let next_epoch_digest = find_next_epoch_digest::<Block>(&block.header)
			.map_err(|e| ConsensusError::from(ConsensusError::ClientImport(e.to_string())))?;

		match (expected_epoch_change, next_epoch_digest.is_some()) {
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
				if !check_roots()? {
					return Err(ConsensusError::ClientImport("Unexpected epoch change".into()));
				}
			},
		}

		// if there's a pending epoch we'll save the previous epoch changes here
		// this way we can revert it if there's any error
		let mut old_epoch_changes = None;

		if let Some(next_epoch) = next_epoch_digest {
			if let Some(enacted_epoch) = enacted_epoch {
				let enacted_epoch = &enacted_epoch.data;
				if next_epoch.epoch_index.checked_sub(enacted_epoch.epoch_index) != Some(1) {
					return Err(ConsensusError::ClientImport(format!(
						"Invalid BABE epoch change: expected next epoch to be {:?}, got {:?}",
						enacted_epoch.epoch_index.saturating_add(1),
						next_epoch.epoch_index,
					)));
				}

				// update the current epoch in the client cache
				new_cache.insert(
					well_known_cache_keys::EPOCH,
					enacted_epoch.encode(),
				);

				let current_epoch = epoch(&*self.api, &BlockId::Hash(parent_hash))?;

				// if the authorities have changed then we populate the
				// `AUTHORITIES` key with the enacted epoch, so that the inner
				// `ImportBlock` can process it (`EPOCH` is specific to BABE).
				// e.g. in the case of GRANDPA it would require a justification
				// for the block, expecting that the authorities actually
				// changed.
				if current_epoch.authorities != enacted_epoch.authorities {
					new_cache.insert(
						well_known_cache_keys::AUTHORITIES,
						enacted_epoch.encode(),
					);
				}
			}

			old_epoch_changes = Some(epoch_changes.clone());

			// track the epoch change in the fork tree
			epoch_changes.import(
				hash,
				number,
				next_epoch,
				&is_descendent_of,
			).map_err(|e| ConsensusError::from(ConsensusError::ClientImport(e.to_string())))?;

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

/// Start an import queue for the BABE consensus algorithm. This method returns
/// the import queue, some data that needs to be passed to the block authoring
/// logic (`BabeLink`), a `BabeBlockImport` which should be used by the
/// authoring when importing its own blocks, and a future that must be run to
/// completion and is responsible for listening to finality notifications and
/// pruning the epoch changes tree.
pub fn import_queue<B, E, Block: BlockT<Hash=H256>, I, RA, PRA, T>(
	config: Config,
	block_import: I,
	justification_import: Option<BoxJustificationImport<Block>>,
	finality_proof_import: Option<BoxFinalityProofImport<Block>>,
	client: Arc<Client<B, E, Block, RA>>,
	api: Arc<PRA>,
	inherent_data_providers: InherentDataProviders,
	transaction_pool: Option<Arc<T>>,
) -> ClientResult<(
	BabeImportQueue<Block>,
	BabeLink,
	BabeBlockImport<B, E, Block, I, RA, PRA>,
	impl futures01::Future<Item = (), Error = ()>,
)> where
	B: Backend<Block, Blake2Hasher> + 'static,
	I: BlockImport<Block> + Clone + Send + Sync + 'static,
	I::Error: Into<ConsensusError>,
	E: CallExecutor<Block, Blake2Hasher> + Clone + Send + Sync + 'static,
	RA: Send + Sync + 'static,
	PRA: ProvideRuntimeApi + HeaderBackend<Block> + ProvideCache<Block> + Send + Sync + AuxStore + 'static,
	PRA::Api: BlockBuilderApi<Block> + BabeApi<Block>,
	T: SubmitExtrinsic + Send + Sync + 'static,
	<T as SubmitExtrinsic>::Api: ChainApi<Block=Block>,
{
	register_babe_inherent_data_provider(&inherent_data_providers, config.get())?;
	initialize_authorities_cache(&*api)?;

	let verifier = BabeVerifier {
		api: api.clone(),
		inherent_data_providers,
		time_source: Default::default(),
		config,
		transaction_pool,
	};

	#[allow(deprecated)]
	let epoch_changes = aux_schema::load_epoch_changes(&**client.backend())?;

	let block_import = BabeBlockImport::new(
		client.clone(),
		api,
		epoch_changes.clone(),
		block_import,
	);

	let pruning_task = client.finality_notification_stream()
		.map(|v| Ok::<_, ()>(v)).compat()
		.for_each(move |notification| {
			let is_descendent_of = is_descendent_of(&client, None);
			epoch_changes.lock().prune(
				&notification.hash,
				*notification.header.number(),
				&is_descendent_of,
			).map_err(|e| {
				debug!(target: "babe", "Error pruning epoch changes fork tree: {:?}", e)
			})?;

			Ok(())
		});

	let timestamp_core = verifier.time_source.clone();
	let queue = BasicQueue::new(
		verifier,
		Box::new(block_import.clone()),
		justification_import,
		finality_proof_import,
	);

	Ok((queue, timestamp_core, block_import, pruning_task))
}

/// BABE test helpers. Utility methods for manually authoring blocks.
#[cfg(feature = "test-helpers")]
pub mod test_helpers {
	use super::*;

	/// Try to claim the given slot and return a `BabePreDigest` if
	/// successful.
	pub fn claim_slot<B, C>(
		client: &C,
		at: &BlockId<B>,
		slot_number: u64,
		c: (u64, u64),
		keystore: &KeyStorePtr,
	) -> Option<BabePreDigest> where
		B: BlockT,
		C: ProvideRuntimeApi + ProvideCache<B>,
		C::Api: BabeApi<B>,
	{
		let epoch = epoch(client, at).unwrap();

		super::claim_slot(
			slot_number,
			epoch,
			c,
			keystore,
		).map(|((inout, vrf_proof, _), authority_index, _)| {
			BabePreDigest {
				vrf_proof,
				vrf_output: inout.to_output(),
				authority_index: authority_index as u32,
				slot_number,
			}
		})
	}
}
