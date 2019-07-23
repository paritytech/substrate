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

#![forbid(unsafe_code, missing_docs, unused_must_use, unused_imports, unused_variables)]
#![cfg_attr(not(test), forbid(dead_code))]
pub use babe_primitives::*;
pub use consensus_common::SyncOracle;
use consensus_common::ImportResult;
use consensus_common::import_queue::{
	BoxJustificationImport, BoxFinalityProofImport,
};
use consensus_common::well_known_cache_keys::Id as CacheKeyId;
use runtime_primitives::{generic, generic::BlockId, Justification};
use runtime_primitives::traits::{
	Block as BlockT, Header, DigestItemFor, NumberFor, ProvideRuntimeApi,
	SimpleBitOps, Zero,
};
use std::{collections::HashMap, sync::Arc, u64, fmt::{Debug, Display}, time::{Instant, Duration}};
use runtime_support::serde::{Serialize, Deserialize};
use parity_codec::{Decode, Encode};
use parking_lot::{Mutex, MutexGuard};
use primitives::{Blake2Hasher, H256, Pair, Public, sr25519};
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
	blockchain::{self, HeaderBackend, ProvideCache},
	BlockchainEvents,
	CallExecutor, Client,
	runtime_api::ApiExt,
	error::Result as ClientResult,
	backend::{AuxStore, Backend},
	utils::is_descendent_of,
};
use fork_tree::ForkTree;
use slots::{CheckedHeader, check_equivocation};
use futures::{Future, IntoFuture, future, stream::Stream};
use futures03::{StreamExt as _, TryStreamExt as _};
use tokio_timer::Timeout;
use log::{error, warn, debug, info, trace};

use slots::{SlotWorker, SlotData, SlotInfo, SlotCompatible, SignedDuration};

mod aux_schema;
#[cfg(test)]
mod tests;
pub use babe_primitives::AuthorityId;

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

	/// Retrieve the threshold for BABE
	pub fn threshold(&self) -> u64 {
		self.0.threshold
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

	/// The key of the node we are running on.
	pub local_key: Arc<sr25519::Pair>,

	/// The client to use
	pub client: Arc<C>,

	/// The SelectChain Strategy
	pub select_chain: SC,

	/// A block importer
	pub block_import: I,

	/// The environment
	pub env: Arc<E>,

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
	local_key,
	client,
	select_chain,
	block_import,
	env,
	sync_oracle,
	inherent_data_providers,
	force_authoring,
	time_source,
}: BabeParams<C, E, I, SO, SC>) -> Result<
	impl Future<Item=(), Error=()>,
	consensus_common::Error,
> where
	B: BlockT<Header=H>,
	C: ProvideRuntimeApi + ProvideCache<B>,
	C::Api: BabeApi<B>,
	SC: SelectChain<B>,
	E::Proposer: Proposer<B, Error=Error>,
	<<E::Proposer as Proposer<B>>::Create as IntoFuture>::Future: Send + 'static,
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
		local_key,
		sync_oracle: sync_oracle.clone(),
		force_authoring,
		threshold: config.threshold(),
	};
	register_babe_inherent_data_provider(&inherent_data_providers, config.0.slot_duration())?;
	Ok(slots::start_slot_worker(
		config.0,
		select_chain,
		worker,
		sync_oracle,
		inherent_data_providers,
		time_source,
	))
}

struct BabeWorker<C, E, I, SO> {
	client: Arc<C>,
	block_import: Arc<Mutex<I>>,
	env: Arc<E>,
	local_key: Arc<sr25519::Pair>,
	sync_oracle: SO,
	force_authoring: bool,
	threshold: u64,
}

impl<Hash, H, B, C, E, I, Error, SO> SlotWorker<B> for BabeWorker<C, E, I, SO> where
	B: BlockT<Header=H, Hash=Hash>,
	C: ProvideRuntimeApi + ProvideCache<B>,
	C::Api: BabeApi<B>,
	E: Environment<B, Error=Error>,
	E::Proposer: Proposer<B, Error=Error>,
	<<E::Proposer as Proposer<B>>::Create as IntoFuture>::Future: Send + 'static,
	Hash: Debug + Eq + Copy + SimpleBitOps + Encode + Decode + Serialize +
		for<'de> Deserialize<'de> + Debug + Default + AsRef<[u8]> + AsMut<[u8]> +
		std::hash::Hash + Display + Send + Sync + 'static,
	H: Header<Hash=B::Hash>,
	I: BlockImport<B> + Send + Sync + 'static,
	SO: SyncOracle + Send + Clone,
	Error: std::error::Error + Send + From<::consensus_common::Error> + From<I::Error> + 'static,
{
	type OnSlot = Box<dyn Future<Item=(), Error=consensus_common::Error> + Send>;

	fn on_slot(
		&self,
		chain_head: B::Header,
		slot_info: SlotInfo,
	) -> Self::OnSlot {
		let pair = self.local_key.clone();
		let ref client = self.client;
		let block_import = self.block_import.clone();
		let ref env = self.env;

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
				return Box::new(future::ok(()));
			}
		};

		let Epoch { ref authorities, randomness, epoch_index, .. } = epoch;

		if authorities.is_empty() {
			error!(target: "babe", "No authorities at block {:?}", chain_head.hash());
		}

		if !self.force_authoring && self.sync_oracle.is_offline() && authorities.len() > 1 {
			debug!(target: "babe", "Skipping proposal slot. Waiting for the network.");
			telemetry!(CONSENSUS_DEBUG; "babe.skipping_proposal_slot";
				"authorities_len" => authorities.len()
			);
			return Box::new(future::ok(()));
		}

		let proposal_work = if let Some(((inout, vrf_proof, _batchable_proof), authority_index)) = claim_slot(
			&randomness,
			slot_info.number,
			epoch_index,
			epoch,
			&pair,
			self.threshold,
		) {
			debug!(
				target: "babe", "Starting authorship at slot {}; timestamp = {}",
				slot_number,
				timestamp,
			);
			telemetry!(CONSENSUS_DEBUG; "babe.starting_authorship";
				"slot_number" => slot_number, "timestamp" => timestamp
			);

			// we are the slot author. make a block and sign it.
			let proposer = match env.init(&chain_head) {
				Ok(p) => p,
				Err(e) => {
					warn!(target: "babe", "Unable to author block in slot {:?}: {:?}", slot_number, e);
					telemetry!(CONSENSUS_WARN; "babe.unable_authoring_block";
						"slot" => slot_number, "err" => ?e
					);
					return Box::new(future::ok(()))
				}
			};

			let inherent_digest = BabePreDigest {
				vrf_proof,
				vrf_output: inout.to_output(),
				authority_index: authority_index as u64,
				slot_number,
			};

			// deadline our production to approx. the end of the slot
			let remaining_duration = slot_info.remaining_duration();
			Timeout::new(
				proposer.propose(
					slot_info.inherent_data,
					generic::Digest {
						logs: vec![
							generic::DigestItem::babe_pre_digest(inherent_digest.clone()),
						],
					},
					remaining_duration,
				).into_future(),
				remaining_duration,
			)
		} else {
			return Box::new(future::ok(()));
		};

		Box::new(proposal_work.map(move |b| {
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
			let signature = pair.sign(header_hash.as_ref());
			let signature_digest_item = DigestItemFor::<B>::babe_seal(signature);

			let cache = find_epoch_digest::<B>(&header)
				.map(|epoch| vec![(well_known_cache_keys::AUTHORITIES, epoch.encode())])
				.map(|keys| keys.into_iter().collect())
				.unwrap_or_default();

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

			if let Err(e) = block_import.lock().import_block(import_block, cache) {
				warn!(target: "babe", "Error with block built on {:?}: {:?}",
						parent_hash, e);
				telemetry!(CONSENSUS_WARN; "babe.err_with_block_built_on";
					"hash" => ?parent_hash, "err" => ?e
				);
			}
		}).map_err(|e| {
			warn!("Client import failed: {:?}", e);
			consensus_common::Error::ClientImport(format!("{:?}", e)).into()
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

/// Extract the BABE pre digest from the given header. Pre-runtime digests are
/// mandatory, the function will return `Err` if none is found.
fn find_pre_digest<B: BlockT>(header: &B::Header) -> Result<BabePreDigest, String>
	where DigestItemFor<B>: CompatibleDigestItem,
{
	for log in header.digest().logs() {
		if let Some(pre_digest) = log.as_babe_pre_digest() {
			return Ok(pre_digest);
		}
	}

	Err(babe_err!("No BABE pre-runtime digest found"))
}

/// Extract the BABE epoch change digest from the given header, if it exists.
fn find_epoch_digest<B: BlockT>(header: &B::Header) -> Option<Epoch>
	where DigestItemFor<B>: CompatibleDigestItem,
{
	for log in header.digest().logs() {
		if let Some(epoch_digest) = log.as_babe_epoch() {
			return Some(epoch_digest);
		}
	}

	return None;
}

/// Check a header has been signed by the right key. If the slot is too far in
/// the future, an error will be returned. If successful, returns the pre-header
/// and the digest item containing the seal.
///
/// The seal must be the last digest.  Otherwise, the whole header is considered
/// unsigned.  This is required for security and must not be changed.
///
/// This digest item will always return `Some` when used with `as_babe_pre_digest`.
// FIXME #1018 needs misbehavior types
fn check_header<B: BlockT + Sized, C: AuxStore>(
	client: &C,
	slot_now: u64,
	mut header: B::Header,
	hash: B::Hash,
	authorities: &[AuthorityId],
	randomness: [u8; 32],
	epoch_index: u64,
	threshold: u64,
) -> Result<CheckedHeader<B::Header, (DigestItemFor<B>, DigestItemFor<B>)>, String>
	where DigestItemFor<B>: CompatibleDigestItem,
{
	trace!(target: "babe", "Checking header");
	let seal = match header.digest_mut().pop() {
		Some(x) => x,
		None => return Err(babe_err!("Header {:?} is unsealed", hash)),
	};

	let sig = seal.as_babe_seal().ok_or_else(|| {
		babe_err!("Header {:?} has a bad seal", hash)
	})?;

	let pre_digest = find_pre_digest::<B>(&header)?;

	let BabePreDigest { slot_number, authority_index, ref vrf_proof, ref vrf_output } = pre_digest;

	if slot_number > slot_now {
		header.digest_mut().push(seal);
		Ok(CheckedHeader::Deferred(header, slot_number))
	} else if authority_index > authorities.len() as u64 {
		Err(babe_err!("Slot author not found"))
	} else {
		let (pre_hash, author) = (header.hash(), &authorities[authority_index as usize]);

		if sr25519::Pair::verify(&sig, pre_hash, author.clone()) {
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

			if !check(&inout, threshold) {
				return Err(babe_err!("VRF verification of block by author {:?} failed: \
									  threshold {} exceeded", author, threshold));
			}

			if let Some(equivocation_proof) = check_equivocation(
				client,
				slot_now,
				slot_number,
				&header,
				author,
			).map_err(|e| e.to_string())? {
				info!(
					"Slot author {:?} is equivocating at slot {} with headers {:?} and {:?}",
					author,
					slot_number,
					equivocation_proof.fst_header().hash(),
					equivocation_proof.snd_header().hash(),
				);
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
pub struct BabeVerifier<C> {
	api: Arc<C>,
	inherent_data_providers: inherents::InherentDataProviders,
	config: Config,
	time_source: BabeLink,
}

impl<C> BabeVerifier<C> {
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
				.try_for_each(|(i, e)| Err(self.inherent_data_providers.error_to_string(&i, &e)))
		} else {
			Ok(())
		}
	}
}

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
				.and_then(|x| x.checked_mul(u128::from(slot_number).saturating_sub(u128::from(sl))))
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

		time_source.1.clear();
		time_source.0.replace(Instant::now() - median);
	} else {
		time_source.1.push((Instant::now(), slot_now))
	}
}

impl<B: BlockT, C> Verifier<B> for BabeVerifier<C> where
	C: ProvideRuntimeApi + Send + Sync + AuxStore + ProvideCache<B>,
	C::Api: BlockBuilderApi<B> + BabeApi<B>,
{
	fn verify(
		&self,
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

		let authorities: Vec<_> = authorities.into_iter().map(|(s, _)| s).collect();

		// We add one to allow for some small drift.
		// FIXME #1019 in the future, alter this queue to allow deferring of headers
		let checked_header = check_header::<B, C>(
			&self.api,
			slot_now + 1,
			header,
			hash,
			&authorities[..],
			randomness,
			epoch_index,
			self.config.threshold(),
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

				// `Consensus` is the Babe-specific authorities change log.
				// It's an encoded `Epoch`, the same format as is stored in the
				// cache, so no need to decode/re-encode.
				let maybe_keys = find_epoch_digest::<B>(&pre_header)
					.map(|epoch| vec![(well_known_cache_keys::AUTHORITIES, epoch.encode())]);

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

				// FIXME: this should eventually be moved to BabeBlockImport
				median_algorithm(
					self.config.0.median_required_blocks,
					self.config.get(),
					slot_number,
					slot_now,
					&mut *self.time_source.0.lock(),
				);

				// FIXME #1019 extract authorities
				Ok((import_block, maybe_keys))
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
		.and_then(|cache| cache.get_at(&well_known_cache_keys::AUTHORITIES, at)
			.and_then(|v| Decode::decode(&mut &v[..])))
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

fn get_keypair(q: &sr25519::Pair) -> &Keypair {
	q.as_ref()
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

fn check(inout: &VRFInOut, threshold: u64) -> bool {
	u64::from_le_bytes(inout.make_bytes::<[u8; 8]>(BABE_VRF_PREFIX)) < threshold
}

/// Claim a slot if it is our turn.  Returns `None` if it is not our turn.
///
/// This hashes the slot number, epoch, genesis hash, and chain randomness into
/// the VRF.  If the VRF produces a value less than `threshold`, it is our turn,
/// so it returns `Some(_)`.  Otherwise, it returns `None`.
fn claim_slot(
	randomness: &[u8],
	slot_number: u64,
	epoch: u64,
	Epoch { ref authorities, .. }: Epoch,
	key: &sr25519::Pair,
	threshold: u64,
) -> Option<((VRFInOut, VRFProof, VRFProofBatchable), usize)> {
	let public = &key.public();
	let authority_index = authorities.iter().position(|s| &s.0 == public)?;
	let transcript = make_transcript(randomness, slot_number, epoch);

	// Compute the threshold we will use.
	//
	// We already checked that authorities contains `key.public()`, so it can't
	// be empty.  Therefore, this division is safe.
	let threshold = threshold / authorities.len() as u64;

	get_keypair(key)
		.vrf_sign_n_check(transcript, |inout| check(inout, threshold))
		.map(|s|(s, authority_index))
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
		.get_at(&well_known_cache_keys::AUTHORITIES, &genesis_id)
		.and_then(|v| Decode::decode(&mut &v[..]));
	if genesis_epoch.is_some() {
		return Ok(());
	}

	let map_err = |error| consensus_common::Error::from(consensus_common::Error::ClientImport(
		format!(
			"Error initializing authorities cache: {}",
			error,
		)));

	let genesis_epoch = epoch(client, &genesis_id)?;
	cache.initialize(&well_known_cache_keys::AUTHORITIES, genesis_epoch.encode())
		.map_err(map_err)
}

/// Tree of all epoch changes across all *seen* forks. Data stored in tree is the
/// hash and block number of the block signaling the epoch change, the new epoch
/// index and the minimum *slot number* when the next epoch should start (i.e.
/// slot number begin + duration).
type EpochChanges<Block> = ForkTree<
	<Block as BlockT>::Hash,
	NumberFor<Block>,
	(u64, SlotNumber),
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
pub struct BabeBlockImport<B, E, Block: BlockT, I, RA> {
	inner: I,
	client: Arc<Client<B, E, Block, RA>>,
	epoch_changes: SharedEpochChanges<Block>,
}

impl<B, E, Block: BlockT, I: Clone, RA> Clone for BabeBlockImport<B, E, Block, I, RA> {
	fn clone(&self) -> Self {
		BabeBlockImport {
			inner: self.inner.clone(),
			client: self.client.clone(),
			epoch_changes: self.epoch_changes.clone(),
		}
	}
}

impl<B, E, Block: BlockT, I, RA> BabeBlockImport<B, E, Block, I, RA> {
	fn new(
		client: Arc<Client<B, E, Block, RA>>,
		epoch_changes: SharedEpochChanges<Block>,
		block_import: I,
	) -> Self {
		BabeBlockImport {
			client,
			inner: block_import,
			epoch_changes,
		}
	}
}

impl<B, E, Block, I, RA> BlockImport<Block> for BabeBlockImport<B, E, Block, I, RA> where
	Block: BlockT<Hash=H256>,
	I: BlockImport<Block> + Send + Sync,
	I::Error: Into<ConsensusError>,
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
	RA: Send + Sync,
{
	type Error = ConsensusError;

	fn import_block(
		&mut self,
		mut block: BlockImportParams<Block>,
		new_cache: HashMap<well_known_cache_keys::Id, Vec<u8>>,
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
			let pre_digest = find_pre_digest::<Block>(&block.header)
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
		let epoch_change = epoch_changes.find_node_where(
			&hash,
			&number,
			&is_descendent_of,
			&|(_, expected_epoch_change_slot)| {
				*expected_epoch_change_slot <= slot_number
			}
		).map_err(|e| ConsensusError::from(ConsensusError::ClientImport(e.to_string())))?;

		let check_roots = || -> Result<bool, ConsensusError> {
			// this can only happen when the chain starts, since there's no epoch change at genesis.
			// afterwards every time we expect an epoch change it means we will import another one.
			for (root, _, _) in epoch_changes.roots() {
				let is_descendent_of = is_descendent_of(root, &hash)
					.map_err(|e| ConsensusError::from(ConsensusError::ClientImport(e.to_string())))?;

				if is_descendent_of {
					return Ok(false);
				}
			}

			Ok(true)
		};

		let expected_epoch_change = epoch_change.is_some();

		match (expected_epoch_change, new_cache.contains_key(&well_known_cache_keys::AUTHORITIES)) {
			(true, true) => {},
			(false, false) => {},
			(true, false) => {
				return Err(
					ConsensusError::ClientImport("Expected epoch change to happen by this block".into())
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

		if let Some(entry) = new_cache.get(&well_known_cache_keys::AUTHORITIES) {
			if let Some(epoch) = Epoch::decode(&mut &entry[..]) {
				if let Some(last_epoch_change) = epoch_change {
					let last_epoch_index = last_epoch_change.data.0;
					if epoch.epoch_index.checked_sub(last_epoch_index) != Some(1) {
						return Err(ConsensusError::ClientImport(format!(
							"Invalid BABE epoch change: expected next epoch to be {:?}, got {:?}",
							last_epoch_index.saturating_add(1),
							epoch.epoch_index,
						)));
					}
				}

				old_epoch_changes = Some(epoch_changes.clone());

				// track the epoch change in the fork tree
				epoch_changes.import(
					hash,
					number,
					(epoch.epoch_index, slot_number + epoch.duration),
					&is_descendent_of,
				).map_err(|e| ConsensusError::from(ConsensusError::ClientImport(e.to_string())))?;

				crate::aux_schema::write_epoch_changes::<Block, _, _>(
					&*epoch_changes,
					|insert| block.auxiliary.extend(
						insert.iter().map(|(k, v)| (k.to_vec(), Some(v.to_vec())))
					)
				);
			} else {
				return Err(
					ConsensusError::ClientImport("Failed to decode epoch change digest".into())
				);
			}
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
pub fn import_queue<B, E, Block: BlockT<Hash=H256>, I, RA, PRA>(
	config: Config,
	block_import: I,
	justification_import: Option<BoxJustificationImport<Block>>,
	finality_proof_import: Option<BoxFinalityProofImport<Block>>,
	client: Arc<Client<B, E, Block, RA>>,
	api: Arc<PRA>,
	inherent_data_providers: InherentDataProviders,
) -> ClientResult<(
	BabeImportQueue<Block>,
	BabeLink,
	BabeBlockImport<B, E, Block, I, RA>,
	impl Future<Item = (), Error = ()>,
)> where
	B: Backend<Block, Blake2Hasher> + 'static,
	I: BlockImport<Block> + Clone + Send + Sync + 'static,
	I::Error: Into<ConsensusError>,
	E: CallExecutor<Block, Blake2Hasher> + Clone + Send + Sync + 'static,
	RA: Send + Sync + 'static,
	PRA: ProvideRuntimeApi + ProvideCache<Block> + Send + Sync + AuxStore + 'static,
	PRA::Api: BlockBuilderApi<Block> + BabeApi<Block>,
{
	register_babe_inherent_data_provider(&inherent_data_providers, config.get())?;
	initialize_authorities_cache(&*api)?;

	let verifier = BabeVerifier {
		api,
		inherent_data_providers,
		time_source: Default::default(),
		config,
	};

	#[allow(deprecated)]
	let epoch_changes = aux_schema::load_epoch_changes(&**client.backend())?;

	let block_import = BabeBlockImport::new(
		client.clone(),
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
			).map_err(|e| debug!(target: "babe", "Error pruning epoch changes fork tree: {:?}", e))?;

			Ok(())
		});

	let timestamp_core = verifier.time_source.clone();
	let queue = BasicQueue::new(
		Arc::new(verifier),
		Box::new(block_import.clone()),
		justification_import,
		finality_proof_import,
	);

	Ok((queue, timestamp_core, block_import, pruning_task))
}
