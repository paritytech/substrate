// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Aura (Authority-round) consensus in substrate.
//!
//! Aura works by having a list of authorities A who are expected to roughly
//! agree on the current time. Time is divided up into discrete slots of t
//! seconds each. For each slot s, the author of that slot is A[s % |A|].
//!
//! The author is allowed to issue one block but not more during that slot,
//! and it will be built upon the longest valid chain that has been seen.
//!
//! Blocks from future steps will be either deferred or rejected depending on how
//! far in the future they are.
#![forbid(missing_docs, unsafe_code)]
use std::{sync::Arc, time::Duration, thread, marker::PhantomData, hash::Hash, fmt::Debug};

use parity_codec::{Encode, Decode};
use consensus_common::{self, Authorities, BlockImport, Environment, Proposer,
	ForkChoiceStrategy, ImportBlock, BlockOrigin, Error as ConsensusError,
	SelectChain, well_known_cache_keys
};
use consensus_common::import_queue::{Verifier, BasicQueue, SharedBlockImport, SharedJustificationImport};
use client::{
	block_builder::api::BlockBuilder as BlockBuilderApi,
	blockchain::ProvideCache,
	runtime_api::{ApiExt, Core as CoreApi},
	error::Result as CResult,
	backend::AuxStore,
};
use aura_primitives::AURA_ENGINE_ID;
use runtime_primitives::{generic, generic::BlockId, Justification};
use runtime_primitives::traits::{
	Block, Header, Digest, DigestItemFor, DigestItem, ProvideRuntimeApi, AuthorityIdFor,
};
use primitives::Pair;
use inherents::{InherentDataProviders, InherentData, RuntimeString};
use authorities::AuthoritiesApi;

use futures::{Future, IntoFuture, future, stream::Stream};
use tokio::timer::Timeout;
use log::{warn, debug, info, trace};

use srml_aura::{
	InherentType as AuraInherent, AuraInherentData,
	timestamp::{TimestampInherentData, InherentType as TimestampInherent, InherentError as TIError}
};
use substrate_telemetry::{telemetry, CONSENSUS_TRACE, CONSENSUS_DEBUG, CONSENSUS_WARN, CONSENSUS_INFO};

use slots::{CheckedHeader, SlotWorker, SlotInfo, SlotCompatible, slot_now};

pub use aura_primitives::*;
pub use consensus_common::{SyncOracle, ExtraVerification};

type AuthorityId<P> = <P as Pair>::Public;
type Signature<P> = <P as Pair>::Signature;

/// A handle to the network. This is generally implemented by providing some
/// handle to a gossip service or similar.
///
/// Intended to be a lightweight handle such as an `Arc`.
#[deprecated(
	since = "1.0.1",
	note = "This is dead code and will be removed in a future release",
)]
pub trait Network: Clone {
	/// A stream of input messages for a topic.
	type In: Stream<Item=Vec<u8>,Error=()>;

	/// Send a message at a specific round out.
	fn send_message(&self, slot: u64, message: Vec<u8>);
}

/// A slot duration. Create with `get_or_compute`.
#[derive(Clone, Copy, Debug, Encode, Decode, Hash, PartialOrd, Ord, PartialEq, Eq)]
pub struct SlotDuration(slots::SlotDuration<u64>);

impl SlotDuration {
	/// Either fetch the slot duration from disk or compute it from the genesis
	/// state.
	pub fn get_or_compute<B: Block, C>(client: &C) -> CResult<Self>
	where
		C: AuxStore, C: ProvideRuntimeApi, C::Api: AuraApi<B>,
	{
		slots::SlotDuration::get_or_compute(client, |a, b| a.slot_duration(b)).map(Self)
	}

	/// Get the slot duration in milliseconds.
	pub fn get(&self) -> u64 {
		self.0.get()
	}
}

/// Get slot author for given block along with authorities.
fn slot_author<P: Pair>(slot_num: u64, authorities: &[AuthorityId<P>]) -> Option<&AuthorityId<P>> {
	if authorities.is_empty() { return None }

	let idx = slot_num % (authorities.len() as u64);
	assert!(idx <= usize::max_value() as u64,
		"It is impossible to have a vector with length beyond the address space; qed");

	let current_author = authorities.get(idx as usize)
		.expect("authorities not empty; index constrained to list length;\
				this is a valid index; qed");

	Some(current_author)
}

fn inherent_to_common_error(err: RuntimeString) -> consensus_common::Error {
	consensus_common::ErrorKind::InherentData(err.into()).into()
}

/// A digest item which is usable with aura consensus.
pub trait CompatibleDigestItem<T: Pair>: Sized {
	/// Construct a digest item which contains a slot number and a signature on the
	/// hash.
	fn aura_seal(slot_num: u64, signature: Signature<T>) -> Self;

	/// If this item is an Aura seal, return the slot number and signature.
	fn as_aura_seal(&self) -> Option<(u64, Signature<T>)>;

	/// Return `true` if this seal type is deprecated.  Otherwise, return
	/// `false`.
	fn is_deprecated(&self) -> bool;
}

impl<P, Hash> CompatibleDigestItem<P> for generic::DigestItem<Hash, P::Public, P::Signature>
	where P: Pair, P::Signature: Clone + Encode + Decode,
{
	/// Construct a digest item which is a slot number and a signature on the
	/// hash.
	fn aura_seal(slot_number: u64, signature: Signature<P>) -> Self {
		generic::DigestItem::Consensus(AURA_ENGINE_ID, (slot_number, signature).encode())
	}

	/// If this item is an Aura seal, return the slot number and signature.
	#[allow(deprecated)]
	fn as_aura_seal(&self) -> Option<(u64, Signature<P>)> {
		match self {
			generic::DigestItem::Seal(slot, ref sig) => Some((*slot, (*sig).clone())),
			generic::DigestItem::Consensus(AURA_ENGINE_ID, seal) => Decode::decode(&mut &seal[..]),
			_ => None,
		}
	}

	#[allow(deprecated)]
	fn is_deprecated(&self) -> bool {
		match self {
			generic::DigestItem::Seal(_, _) => true,
			_ => false,
		}
	}
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct AuraSlotCompatible;

impl SlotCompatible for AuraSlotCompatible {
	fn extract_timestamp_and_slot(
		data: &InherentData
	) -> Result<(TimestampInherent, AuraInherent), consensus_common::Error> {
		data.timestamp_inherent_data()
			.and_then(|t| data.aura_inherent_data().map(|a| (t, a)))
			.map_err(inherent_to_common_error)
	}
}

/// Start the aura worker in a separate thread.
#[deprecated(since = "1.1", note = "Please spawn a thread manually")]
pub fn start_aura_thread<B, C, SC, E, I, P, SO, Error, OnExit>(
	slot_duration: SlotDuration,
	local_key: Arc<P>,
	client: Arc<C>,
	select_chain: SC,
	block_import: Arc<I>,
	env: Arc<E>,
	sync_oracle: SO,
	on_exit: OnExit,
	inherent_data_providers: InherentDataProviders,
	force_authoring: bool,
) -> Result<(), consensus_common::Error> where
	B: Block + 'static,
	C: ProvideRuntimeApi + ProvideCache<B> + Send + Sync + 'static,
	C::Api: AuthoritiesApi<B>,
	SC: SelectChain<B> + Clone + 'static,
	E: Environment<B, Error=Error> + Send + Sync + 'static,
	E::Proposer: Proposer<B, Error=Error> + Send + 'static,
	<<E::Proposer as Proposer<B>>::Create as IntoFuture>::Future: Send + 'static,
	I: BlockImport<B> + Send + Sync + 'static,
	Error: From<I::Error> + 'static,
	P: Pair + Send + Sync + 'static,
	P::Public: Encode + Decode + Eq + Clone + Debug + Hash + Send + Sync + 'static,
	P::Signature: Encode,
	SO: SyncOracle + Send + Sync + Clone + 'static,
	OnExit: Future<Item=(), Error=()> + Send + 'static,
	DigestItemFor<B>: CompatibleDigestItem<P> + DigestItem<AuthorityId=AuthorityId<P>> + 'static,
	Error: ::std::error::Error + Send + From<::consensus_common::Error> + 'static,
{
	let worker = AuraWorker {
		client: client.clone(),
		block_import,
		env,
		local_key,
		inherent_data_providers: inherent_data_providers.clone(),
		sync_oracle: sync_oracle.clone(),
		force_authoring,
	};

	#[allow(deprecated)]	// The function we are in is also deprecated.
	slots::start_slot_worker_thread::<_, _, _, _, AuraSlotCompatible, u64, _>(
		slot_duration.0,
		select_chain,
		Arc::new(worker),
		sync_oracle,
		on_exit,
		inherent_data_providers
	)
}

/// Start the aura worker. The returned future should be run in a tokio runtime.
pub fn start_aura<B, C, SC, E, I, P, SO, Error, OnExit>(
	slot_duration: SlotDuration,
	local_key: Arc<P>,
	client: Arc<C>,
	select_chain: SC,
	block_import: Arc<I>,
	env: Arc<E>,
	sync_oracle: SO,
	on_exit: OnExit,
	inherent_data_providers: InherentDataProviders,
	force_authoring: bool,
) -> Result<impl Future<Item=(), Error=()>, consensus_common::Error> where
	B: Block,
	C: ProvideRuntimeApi + ProvideCache<B>,
	C::Api: AuthoritiesApi<B>,
	SC: SelectChain<B> + Clone,
	E: Environment<B, Error=Error>,
	E::Proposer: Proposer<B, Error=Error>,
	<<E::Proposer as Proposer<B>>::Create as IntoFuture>::Future: Send + 'static,
	I: BlockImport<B> + Send + Sync + 'static,
	P: Pair + Send + Sync + 'static,
	P::Public: Hash + Eq + Send + Sync + Clone + Debug + Encode + Decode + 'static,
	P::Signature: Encode,
	SO: SyncOracle + Send + Sync + Clone,
	DigestItemFor<B>: CompatibleDigestItem<P> + DigestItem<AuthorityId=AuthorityId<P>>,
	Error: ::std::error::Error + Send + From<::consensus_common::Error> + From<I::Error> + 'static,
	OnExit: Future<Item=(), Error=()>,
{
	let worker = AuraWorker {
		client: client.clone(),
		block_import,
		env,
		local_key,
		inherent_data_providers: inherent_data_providers.clone(),
		sync_oracle: sync_oracle.clone(),
		force_authoring,
	};
	slots::start_slot_worker::<_, _, _, _, _, AuraSlotCompatible, _>(
		slot_duration.0,
		select_chain,
		Arc::new(worker),
		sync_oracle,
		on_exit,
		inherent_data_providers
	)
}

struct AuraWorker<C, E, I, P, SO> {
	client: Arc<C>,
	block_import: Arc<I>,
	env: Arc<E>,
	local_key: Arc<P>,
	sync_oracle: SO,
	inherent_data_providers: InherentDataProviders,
	force_authoring: bool,
}

impl<B: Block, C, E, I, P, Error, SO> SlotWorker<B> for AuraWorker<C, E, I, P, SO> where
	C: ProvideRuntimeApi + ProvideCache<B>,
	C::Api: AuthoritiesApi<B>,
	E: Environment<B, Error=Error>,
	E::Proposer: Proposer<B, Error=Error>,
	<<E::Proposer as Proposer<B>>::Create as IntoFuture>::Future: Send + 'static,
	I: BlockImport<B> + Send + Sync + 'static,
	P: Pair + Send + Sync + 'static,
	P::Public: Hash + Eq + Send + Sync + Clone + Debug + Encode + Decode + 'static,
	P::Signature: Encode,
	SO: SyncOracle + Send + Clone,
	DigestItemFor<B>: CompatibleDigestItem<P> + DigestItem<AuthorityId=AuthorityId<P>>,
	Error: ::std::error::Error + Send + From<::consensus_common::Error> + From<I::Error> + 'static,
{
	type OnSlot = Box<Future<Item=(), Error=consensus_common::Error> + Send>;

	fn on_start(
		&self,
		slot_duration: u64
	) -> Result<(), consensus_common::Error> {
		register_aura_inherent_data_provider(&self.inherent_data_providers, slot_duration)
	}

	fn on_slot(
		&self,
		chain_head: B::Header,
		slot_info: SlotInfo,
	) -> Self::OnSlot {
		let pair = self.local_key.clone();
		let public_key = self.local_key.public();
		let client = self.client.clone();
		let block_import = self.block_import.clone();
		let env = self.env.clone();

		let (timestamp, slot_num, slot_duration) =
			(slot_info.timestamp, slot_info.number, slot_info.duration);

		let authorities = match authorities(client.as_ref(), &BlockId::Hash(chain_head.hash())) {
			Ok(authorities) => authorities,
			Err(e) => {
				warn!(
					"Unable to fetch authorities at block {:?}: {:?}",
					chain_head.hash(),
					e
				);
				telemetry!(CONSENSUS_WARN; "aura.unable_fetching_authorities";
					"slot" => ?chain_head.hash(), "err" => ?e
				);
				return Box::new(future::ok(()));
			}
		};

		if !self.force_authoring && self.sync_oracle.is_offline() && authorities.len() > 1 {
			debug!(target: "aura", "Skipping proposal slot. Waiting for the network.");
			telemetry!(CONSENSUS_DEBUG; "aura.skipping_proposal_slot";
				"authorities_len" => authorities.len()
			);
			return Box::new(future::ok(()));
		}
		let maybe_author = slot_author::<P>(slot_num, &authorities);
		let proposal_work = match maybe_author {
			None => return Box::new(future::ok(())),
			Some(author) => if author == &public_key {
				debug!(
					target: "aura", "Starting authorship at slot {}; timestamp = {}",
					slot_num,
					timestamp
				);
				telemetry!(CONSENSUS_DEBUG; "aura.starting_authorship";
					"slot_num" => slot_num, "timestamp" => timestamp
				);

				// we are the slot author. make a block and sign it.
				let proposer = match env.init(&chain_head, &authorities) {
					Ok(p) => p,
					Err(e) => {
						warn!("Unable to author block in slot {:?}: {:?}", slot_num, e);
						telemetry!(CONSENSUS_WARN; "aura.unable_authoring_block";
							"slot" => slot_num, "err" => ?e
						);
						return Box::new(future::ok(()))
					}
				};

				let remaining_duration = slot_info.remaining_duration();
				// deadline our production to approx. the end of the
				// slot
				Timeout::new(
					proposer.propose(slot_info.inherent_data, remaining_duration).into_future(),
					remaining_duration,
				)
			} else {
				return Box::new(future::ok(()));
			}
		};

		Box::new(
			proposal_work
				.map(move |b| {
					// minor hack since we don't have access to the timestamp
					// that is actually set by the proposer.
					let slot_after_building = slot_now(slot_duration);
					if slot_after_building != Some(slot_num) {
						info!(
							"Discarding proposal for slot {}; block production took too long",
							slot_num
						);
						telemetry!(CONSENSUS_INFO; "aura.discarding_proposal_took_too_long";
							"slot" => slot_num
						);
						return
					}

					let (header, body) = b.deconstruct();
					let header_num = header.number().clone();
					let pre_hash = header.hash();
					let parent_hash = header.parent_hash().clone();

					// sign the pre-sealed hash of the block and then
					// add it to a digest item.
					let to_sign = (slot_num, pre_hash).encode();
					let signature = pair.sign(&to_sign[..]);
					let item = <DigestItemFor<B> as CompatibleDigestItem<P>>::aura_seal(
						slot_num,
						signature,
					);

					let import_block: ImportBlock<B> = ImportBlock {
						origin: BlockOrigin::Own,
						header,
						justification: None,
						post_digests: vec![item],
						body: Some(body),
						finalized: false,
						auxiliary: Vec::new(),
						fork_choice: ForkChoiceStrategy::LongestChain,
					};

					info!("Pre-sealed block for proposal at {}. Hash now {:?}, previously {:?}.",
						  header_num,
						  import_block.post_header().hash(),
						  pre_hash
					);
					telemetry!(CONSENSUS_INFO; "aura.pre_sealed_block";
						"header_num" => ?header_num,
						"hash_now" => ?import_block.post_header().hash(),
						"hash_previously" => ?pre_hash
					);

					if let Err(e) = block_import.import_block(import_block, Default::default()) {
						warn!(target: "aura", "Error with block built on {:?}: {:?}",
							  parent_hash, e);
						telemetry!(CONSENSUS_WARN; "aura.err_with_block_built_on";
							"hash" => ?parent_hash, "err" => ?e
						);
					}
				})
				.map_err(|e| consensus_common::ErrorKind::ClientImport(format!("{:?}", e)).into())
		)
	}
}

/// check a header has been signed by the right key. If the slot is too far in the future, an error will be returned.
/// if it's successful, returns the pre-header and the digest item containing the seal.
///
/// This digest item will always return `Some` when used with `as_aura_seal`.
//
// FIXME #1018 needs misbehavior types
fn check_header<B: Block, P: Pair>(
	slot_now: u64,
	mut header: B::Header,
	hash: B::Hash,
	authorities: &[AuthorityId<P>],
	allow_old_seals: bool,
) -> Result<CheckedHeader<B::Header, DigestItemFor<B>>, String>
	where DigestItemFor<B>: CompatibleDigestItem<P>,
		P::Public: AsRef<P::Public>,
		P::Signature: Decode,
{
	let digest_item = match header.digest_mut().pop() {
		Some(x) => x,
		None => return Err(format!("Header {:?} is unsealed", hash)),
	};

	if !allow_old_seals && digest_item.is_deprecated() {
		debug!(target: "aura", "Header {:?} uses old seal format, rejecting", hash);
		return Err(format!("Header {:?} uses old seal format, rejecting", hash))
	}

	let (slot_num, sig) = digest_item.as_aura_seal().ok_or_else(|| {
		debug!(target: "aura", "Header {:?} is unsealed", hash);
		format!("Header {:?} is unsealed", hash)
	})?;

	if slot_num > slot_now {
		header.digest_mut().push(digest_item);
		Ok(CheckedHeader::Deferred(header, slot_num))
	} else {
		// check the signature is valid under the expected authority and
		// chain state.
		let expected_author = match slot_author::<P>(slot_num, &authorities) {
			None => return Err("Slot Author not found".to_string()),
			Some(author) => author,
		};

		let pre_hash = header.hash();
		let to_sign = (slot_num, pre_hash).encode();
		let public = expected_author;

		if P::verify(&sig, &to_sign[..], public) {
			Ok(CheckedHeader::Checked(header, digest_item))
		} else {
			Err(format!("Bad signature on {:?}", hash))
		}
	}
}

/// A verifier for Aura blocks.
pub struct AuraVerifier<C, E, P> {
	client: Arc<C>,
	extra: E,
	phantom: PhantomData<P>,
	inherent_data_providers: inherents::InherentDataProviders,
	allow_old_seals: bool,
}

impl<C, E, P> AuraVerifier<C, E, P>
	where P: Send + Sync + 'static
{
	fn check_inherents<B: Block>(
		&self,
		block: B,
		block_id: BlockId<B>,
		inherent_data: InherentData,
		timestamp_now: u64,
	) -> Result<(), String>
		where C: ProvideRuntimeApi, C::Api: BlockBuilderApi<B>
	{
		const MAX_TIMESTAMP_DRIFT_SECS: u64 = 60;

		let inherent_res = self.client.runtime_api().check_inherents(
			&block_id,
			block,
			inherent_data,
		).map_err(|e| format!("{:?}", e))?;

		if !inherent_res.ok() {
			inherent_res
				.into_errors()
				.try_for_each(|(i, e)| match TIError::try_from(&i, &e) {
					Some(TIError::ValidAtTimestamp(timestamp)) => {
						// halt import until timestamp is valid.
						// reject when too far ahead.
						if timestamp > timestamp_now + MAX_TIMESTAMP_DRIFT_SECS {
							return Err("Rejecting block too far in future".into());
						}

						let diff = timestamp.saturating_sub(timestamp_now);
						info!(
							target: "aura",
							"halting for block {} seconds in the future",
							diff
						);
						telemetry!(CONSENSUS_INFO; "aura.halting_for_future_block";
							"diff" => ?diff
						);
						thread::sleep(Duration::from_secs(diff));
						Ok(())
					},
					Some(TIError::Other(e)) => Err(e.into()),
					None => Err(self.inherent_data_providers.error_to_string(&i, &e)),
				})
		} else {
			Ok(())
		}
	}
}

/// No-op extra verification.
#[derive(Debug, Clone, Copy)]
pub struct NothingExtra;

impl<B: Block> ExtraVerification<B> for NothingExtra {
	type Verified = Result<(), String>;

	fn verify(&self, _: &B::Header, _: Option<&[B::Extrinsic]>) -> Self::Verified {
		Ok(())
	}
}

#[forbid(deprecated)]
impl<B: Block, C, E, P> Verifier<B> for AuraVerifier<C, E, P> where
	C: ProvideRuntimeApi + Send + Sync,
	C::Api: BlockBuilderApi<B>,
	DigestItemFor<B>: CompatibleDigestItem<P> + DigestItem<AuthorityId=AuthorityId<P>>,
	E: ExtraVerification<B>,
	P: Pair + Send + Sync + 'static,
	P::Public: Send + Sync + Hash + Eq + Clone + Decode + Encode + Debug + AsRef<P::Public> + 'static,
	P::Signature: Encode + Decode,
	Self: Authorities<B>,
{
	fn verify(
		&self,
		origin: BlockOrigin,
		header: B::Header,
		justification: Option<Justification>,
		mut body: Option<Vec<B::Extrinsic>>,
	) -> Result<(ImportBlock<B>, Option<Vec<AuthorityId<P>>>), String> {
		let mut inherent_data = self.inherent_data_providers.create_inherent_data().map_err(String::from)?;
		let (timestamp_now, slot_now) = AuraSlotCompatible::extract_timestamp_and_slot(&inherent_data)
			.map_err(|e| format!("Could not extract timestamp and slot: {:?}", e))?;
		let hash = header.hash();
		let parent_hash = *header.parent_hash();
		let authorities = self.authorities(&BlockId::Hash(parent_hash))
			.map_err(|e| format!("Could not fetch authorities at {:?}: {:?}", parent_hash, e))?;

		let extra_verification = self.extra.verify(
			&header,
			body.as_ref().map(|x| &x[..]),
		);

		// we add one to allow for some small drift.
		// FIXME #1019 in the future, alter this queue to allow deferring of headers
		let checked_header = check_header::<B, P>(
			slot_now + 1,
			header,
			hash,
			&authorities[..],
			self.allow_old_seals,
		)?;
		match checked_header {
			CheckedHeader::Checked(pre_header, seal) => {
				let (slot_num, _) = seal.as_aura_seal()
					.expect("check_header always returns a seal digest item; qed");

				// if the body is passed through, we need to use the runtime
				// to check that the internally-set timestamp in the inherents
				// actually matches the slot set in the seal.
				if let Some(inner_body) = body.take() {
					inherent_data.aura_replace_inherent_data(slot_num);
					let block = B::new(pre_header.clone(), inner_body);

					// skip the inherents verification if the runtime API is old.
					if self.client
						.runtime_api()
						.has_api_with::<BlockBuilderApi<B>, _>(&BlockId::Hash(parent_hash), |v| v >= 2)
						.map_err(|e| format!("{:?}", e))?
					{
						self.check_inherents(
							block.clone(),
							BlockId::Hash(parent_hash),
							inherent_data,
							timestamp_now,
						)?;
					}

					let (_, inner_body) = block.deconstruct();
					body = Some(inner_body);
				}

				trace!(target: "aura", "Checked {:?}; importing.", pre_header);
				telemetry!(CONSENSUS_TRACE; "aura.checked_and_importing"; "pre_header" => ?pre_header);

				extra_verification.into_future().wait()?;

				let import_block = ImportBlock {
					origin,
					header: pre_header,
					post_digests: vec![seal],
					body,
					finalized: false,
					justification,
					auxiliary: Vec::new(),
					fork_choice: ForkChoiceStrategy::LongestChain,
				};

				// FIXME #1019 extract authorities
				Ok((import_block, None))
			}
			CheckedHeader::Deferred(a, b) => {
				debug!(target: "aura", "Checking {:?} failed; {:?}, {:?}.", hash, a, b);
				telemetry!(CONSENSUS_DEBUG; "aura.header_too_far_in_future";
					"hash" => ?hash, "a" => ?a, "b" => ?b
				);
				Err(format!("Header {:?} rejected: too far in the future", hash))
			}
		}
	}
}

impl<B, C, E, P> Authorities<B> for AuraVerifier<C, E, P> where
	B: Block,
	C: ProvideRuntimeApi + ProvideCache<B>,
	C::Api: AuthoritiesApi<B>,
{
	type Error = ConsensusError;

	fn authorities(&self, at: &BlockId<B>) -> Result<Vec<AuthorityIdFor<B>>, Self::Error> {
		authorities(self.client.as_ref(), at)
	}
}

#[allow(deprecated)]
fn authorities<B, C>(client: &C, at: &BlockId<B>) -> Result<Vec<AuthorityIdFor<B>>, ConsensusError> where
	B: Block,
	C: ProvideRuntimeApi + ProvideCache<B>,
	C::Api: AuthoritiesApi<B>,
{
	client
		.cache()
		.and_then(|cache| cache.get_at(&well_known_cache_keys::AUTHORITIES, at)
			.and_then(|v| Decode::decode(&mut &v[..])))
		.or_else(|| {
			if client.runtime_api().has_api::<AuthoritiesApi<B>>(at).unwrap_or(false) {
				AuthoritiesApi::authorities(&*client.runtime_api(), at).ok()
			} else {
				CoreApi::authorities(&*client.runtime_api(), at).ok()
			}
		}).ok_or_else(|| consensus_common::ErrorKind::InvalidAuthoritiesSet.into())
}

/// The Aura import queue type.
pub type AuraImportQueue<B> = BasicQueue<B>;

/// Register the aura inherent data provider, if not registered already.
fn register_aura_inherent_data_provider(
	inherent_data_providers: &InherentDataProviders,
	slot_duration: u64,
) -> Result<(), consensus_common::Error> {
	if !inherent_data_providers.has_provider(&srml_aura::INHERENT_IDENTIFIER) {
		inherent_data_providers
			.register_provider(srml_aura::InherentDataProvider::new(slot_duration))
			.map_err(inherent_to_common_error)
	} else {
		Ok(())
	}
}

/// Start an import queue for the Aura consensus algorithm.
pub fn import_queue<B, C, E, P>(
	slot_duration: SlotDuration,
	block_import: SharedBlockImport<B>,
	justification_import: Option<SharedJustificationImport<B>>,
	client: Arc<C>,
	extra: E,
	inherent_data_providers: InherentDataProviders,
) -> Result<AuraImportQueue<B>, consensus_common::Error> where
	B: Block,
	C: 'static + ProvideRuntimeApi + ProvideCache<B> + Send + Sync,
	C::Api: BlockBuilderApi<B> + AuthoritiesApi<B>,
	DigestItemFor<B>: CompatibleDigestItem<P> + DigestItem<AuthorityId=AuthorityId<P>>,
	E: 'static + ExtraVerification<B>,
	P: Pair + Send + Sync + 'static,
	P::Public: Clone + Eq + Send + Sync + Hash + Debug + Encode + Decode + AsRef<P::Public>,
	P::Signature: Encode + Decode,
{
	register_aura_inherent_data_provider(&inherent_data_providers, slot_duration.get())?;

	let verifier = Arc::new(
		AuraVerifier {
			client: client.clone(),
			extra,
			inherent_data_providers,
			phantom: PhantomData,
			allow_old_seals: false,
		}
	);
	Ok(BasicQueue::new(verifier, block_import, justification_import))
}

/// Start an import queue for the Aura consensus algorithm with backwards compatibility.
#[deprecated(
	since = "1.0.1",
	note = "should not be used unless backwards compatibility with an older chain is needed.",
)]
pub fn import_queue_accept_old_seals<B, C, E, P>(
	slot_duration: SlotDuration,
	block_import: SharedBlockImport<B>,
	justification_import: Option<SharedJustificationImport<B>>,
	client: Arc<C>,
	extra: E,
	inherent_data_providers: InherentDataProviders,
) -> Result<AuraImportQueue<B>, consensus_common::Error> where
	B: Block,
	C: 'static + ProvideRuntimeApi + ProvideCache<B> + Send + Sync,
	C::Api: BlockBuilderApi<B> + AuthoritiesApi<B>,
	DigestItemFor<B>: CompatibleDigestItem<P> + DigestItem<AuthorityId=AuthorityId<P>>,
	E: 'static + ExtraVerification<B>,
	P: Pair + Send + Sync + 'static,
	P::Public: Clone + Eq + Send + Sync + Hash + Debug + Encode + Decode + AsRef<P::Public>,
	P::Signature: Encode + Decode,
{
	register_aura_inherent_data_provider(&inherent_data_providers, slot_duration.get())?;

	let verifier = Arc::new(
		AuraVerifier {
			client: client.clone(),
			extra,
			inherent_data_providers,
			phantom: PhantomData,
			allow_old_seals: true,
		}
	);
	Ok(BasicQueue::new(verifier, block_import, justification_import))
}

#[cfg(test)]
mod tests {
	use super::*;
	use consensus_common::NoNetwork as DummyOracle;
	use network::test::*;
	use network::test::{Block as TestBlock, PeersClient};
	use runtime_primitives::traits::Block as BlockT;
	use network::config::ProtocolConfig;
	use parking_lot::Mutex;
	use tokio::runtime::current_thread;
	use keyring::sr25519::Keyring;
	use primitives::sr25519;
	use client::{LongestChain, BlockchainEvents};
	use test_client;

	type Error = client::error::Error;

	type TestClient = client::Client<test_client::Backend, test_client::Executor, TestBlock, test_client::runtime::RuntimeApi>;

	struct DummyFactory(Arc<TestClient>);
	struct DummyProposer(u64, Arc<TestClient>);

	impl Environment<TestBlock> for DummyFactory {
		type Proposer = DummyProposer;
		type Error = Error;

		fn init(&self, parent_header: &<TestBlock as BlockT>::Header, _authorities: &[AuthorityId<sr25519::Pair>])
			-> Result<DummyProposer, Error>
		{
			Ok(DummyProposer(parent_header.number + 1, self.0.clone()))
		}
	}

	impl Proposer<TestBlock> for DummyProposer {
		type Error = Error;
		type Create = Result<TestBlock, Error>;

		fn propose(&self, _: InherentData, _: Duration) -> Result<TestBlock, Error> {
			self.1.new_block().unwrap().bake().map_err(|e| e.into())
		}
	}

	const SLOT_DURATION: u64 = 1;
	const TEST_ROUTING_INTERVAL: Duration = Duration::from_millis(50);

	pub struct AuraTestNet {
		peers: Vec<Arc<Peer<(), DummySpecialization>>>,
		started: bool,
	}

	impl TestNetFactory for AuraTestNet {
		type Specialization = DummySpecialization;
		type Verifier = AuraVerifier<PeersClient, NothingExtra, sr25519::Pair>;
		type PeerData = ();

		/// Create new test network with peers and given config.
		fn from_config(_config: &ProtocolConfig) -> Self {
			AuraTestNet {
				peers: Vec::new(),
				started: false,
			}
		}

		fn make_verifier(&self, client: Arc<PeersClient>, _cfg: &ProtocolConfig)
			-> Arc<Self::Verifier>
		{
			let slot_duration = SlotDuration::get_or_compute(&*client)
				.expect("slot duration available");
			let inherent_data_providers = InherentDataProviders::new();
			register_aura_inherent_data_provider(
				&inherent_data_providers,
				slot_duration.get()
			).expect("Registers aura inherent data provider");

			assert_eq!(slot_duration.get(), SLOT_DURATION);
			Arc::new(AuraVerifier {
				client,
				extra: NothingExtra,
				inherent_data_providers,
				phantom: Default::default(),
				allow_old_seals: false,
			})
		}

		fn peer(&self, i: usize) -> &Peer<Self::PeerData, DummySpecialization> {
			&self.peers[i]
		}

		fn peers(&self) -> &Vec<Arc<Peer<Self::PeerData, DummySpecialization>>> {
			&self.peers
		}

		fn mut_peers<F: FnOnce(&mut Vec<Arc<Peer<Self::PeerData, DummySpecialization>>>)>(&mut self, closure: F) {
			closure(&mut self.peers);
		}

		fn started(&self) -> bool {
			self.started
		}

		fn set_started(&mut self, new: bool) {
			self.started = new;
		}
	}

	#[test]
	fn authoring_blocks() {
		let _ = ::env_logger::try_init();
		let mut net = AuraTestNet::new(3);

		net.start();

		let peers = &[
			(0, Keyring::Alice),
			(1, Keyring::Bob),
			(2, Keyring::Charlie),
		];

		let net = Arc::new(Mutex::new(net));
		let mut import_notifications = Vec::new();

		let mut runtime = current_thread::Runtime::new().unwrap();
		for (peer_id, key) in peers {
			let client = net.lock().peer(*peer_id).client().clone();
			let select_chain = LongestChain::new(
				client.backend().clone(),
				client.import_lock().clone(),
			);
			let environ = Arc::new(DummyFactory(client.clone()));
			import_notifications.push(
				client.import_notification_stream()
					.take_while(|n| Ok(!(n.origin != BlockOrigin::Own && n.header.number() < &5)))
					.for_each(move |_| Ok(()))
			);

			let slot_duration = SlotDuration::get_or_compute(&*client)
				.expect("slot duration available");

			let inherent_data_providers = InherentDataProviders::new();
			register_aura_inherent_data_provider(
				&inherent_data_providers, slot_duration.get()
			).expect("Registers aura inherent data provider");

			let aura = start_aura::<_, _, _, _, _, sr25519::Pair, _, _, _>(
				slot_duration,
				Arc::new(key.clone().into()),
				client.clone(),
				select_chain,
				client,
				environ.clone(),
				DummyOracle,
				futures::empty(),
				inherent_data_providers,
				false,
			).expect("Starts aura");

			runtime.spawn(aura);
		}

		// wait for all finalized on each.
		let wait_for = ::futures::future::join_all(import_notifications)
			.map(|_| ())
			.map_err(|_| ());

		let drive_to_completion = ::tokio::timer::Interval::new_interval(TEST_ROUTING_INTERVAL)
			.for_each(move |_| {
				net.lock().send_import_notifications();
				net.lock().sync_without_disconnects();
				Ok(())
			})
			.map(|_| ())
			.map_err(|_| ());

		runtime.block_on(wait_for.select(drive_to_completion).map_err(|_| ())).unwrap();
	}

	#[test]
	fn authorities_call_works() {
		let client = test_client::new();

		assert_eq!(client.info().unwrap().chain.best_number, 0);
		assert_eq!(authorities(&client, &BlockId::Number(0)).unwrap(), vec![
			Keyring::Alice.into(),
			Keyring::Bob.into(),
			Keyring::Charlie.into()
		]);
	}
}
