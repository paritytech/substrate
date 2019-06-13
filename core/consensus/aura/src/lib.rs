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
use std::{
	sync::Arc, time::Duration, thread, marker::PhantomData, hash::Hash,
	fmt::Debug, ops::Deref,
};

use parity_codec::{Encode, Decode};
use consensus_common::{self, Authorities, BlockImport, Environment, Proposer,
	ForkChoiceStrategy, ImportBlock, BlockOrigin, Error as ConsensusError,
	SelectChain, well_known_cache_keys,
};
use consensus_common::import_queue::{
	Verifier, BasicQueue, SharedBlockImport, SharedJustificationImport,
	SharedFinalityProofImport, SharedFinalityProofRequestBuilder
};
use client::{
	block_builder::api::BlockBuilder as BlockBuilderApi,
	blockchain::ProvideCache, runtime_api::ApiExt, error::Result as CResult,
	backend::AuxStore,
};
use aura_primitives::slot_author;
use runtime_primitives::{generic::{self, BlockId}, Justification};
use runtime_primitives::traits::{
	Block, Header, Digest, DigestItemFor, DigestItem, ProvideRuntimeApi,
	AuthorityIdFor, Zero, Member, Verify,
};
use primitives::{ed25519, Pair};
use inherents::{InherentDataProviders, InherentData};
use authorities::AuthoritiesApi;

use futures::{Future, IntoFuture, future};
use tokio_timer::Timeout;
use log::{error, warn, debug, info, trace};
use transaction_pool::txpool::{self, PoolApi};

use srml_aura::{
	InherentType as AuraInherent, AuraInherentData,
	timestamp::{
		TimestampInherentData, InherentType as TimestampInherent,
		InherentError as TIError
	}
};
use substrate_telemetry::{
	telemetry, CONSENSUS_TRACE, CONSENSUS_DEBUG, CONSENSUS_WARN,
	CONSENSUS_INFO
};

use slots::{
	CheckedHeader, SlotWorker, SlotInfo, SlotCompatible, slot_now,
	check_equivocation, SlotData,
};
use safety_primitives::AuthorEquivProof;
use node_runtime::{Call, AuraCall};
use consensus_safety::SubmitReport;

pub use aura_primitives::*;
pub use consensus_common::{SyncOracle, ExtraVerification};

type AuthorityId<P> = <P as Pair>::Public;

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


#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct AuraSlotCompatible;

impl SlotCompatible for AuraSlotCompatible {
	fn extract_timestamp_and_slot(
		data: &InherentData
	) -> Result<(TimestampInherent, AuraInherent), consensus_common::Error> {
		data.timestamp_inherent_data()
			.and_then(|t| data.aura_inherent_data().map(|a| (t, a)))
			.map_err(Into::into)
			.map_err(consensus_common::Error::InherentData)
	}
}

/// Start the aura worker. The returned future should be run in a tokio runtime.
pub fn start_aura<B, C, SC, E, I, SO, Error, H>(
	slot_duration: SlotDuration,
	local_key: Arc<ed25519::Pair>,
	client: Arc<C>,
	select_chain: SC,
	block_import: Arc<I>,
	env: Arc<E>,
	sync_oracle: SO,
	inherent_data_providers: InherentDataProviders,
	force_authoring: bool,
) -> Result<impl Future<Item=(), Error=()>, consensus_common::Error> where
	B: Block<Header=H>,
	C: ProvideRuntimeApi + ProvideCache<B> + AuxStore + Send + Sync,
	C::Api: AuthoritiesApi<B>,
	SC: SelectChain<B>,
	// generic::DigestItem<B::Hash, ed25519::Public, ed25519::Signature>: DigestItem<Hash=B::Hash>,
	E::Proposer: Proposer<B, Error=Error>,
	<<E::Proposer as Proposer<B>>::Create as IntoFuture>::Future: Send + 'static,
	// P: Pair + Send + Sync + 'static,
	// ed25519::Public: PartialEq<<P as Pair>::Public> + AsRef<<P as Pair>::Public>,
	// ed25519::Signature: AsRef<<P as Pair>::Signature>,
	// P::Public: Hash + Member + Encode + Decode,
	// P::Signature: Hash + Member + Encode + Decode + Verify,
	// <<P as Pair>::Signature as Verify>::Signer: PartialEq + Encode + Decode + Clone,
	// DigestItemFor<B>: CompatibleDigestItem + DigestItem<AuthorityId=ed25519::Public>,
	H: Header<
		Digest=generic::Digest<generic::DigestItem<B::Hash, ed25519::Public, ed25519::Signature>>,
		Hash=B::Hash,
	>,
	E: Environment<B, Error=Error>,
	I: BlockImport<B> + Send + Sync + 'static,
	Error: ::std::error::Error + Send + From<::consensus_common::Error> + From<I::Error> + 'static,
	SO: SyncOracle + Send + Sync + Clone,
{
	let worker = AuraWorker {
		client: client.clone(),
		block_import,
		env,
		local_key,
		sync_oracle: sync_oracle.clone(),
		force_authoring,
	};
	register_aura_inherent_data_provider(
		&inherent_data_providers,
		slot_duration.0.slot_duration()
	)?;
	Ok(slots::start_slot_worker::<_, _, _, _, _, AuraSlotCompatible>(
		slot_duration.0,
		select_chain,
		worker,
		sync_oracle,
		inherent_data_providers
	))
}

struct AuraWorker<C, E, I, SO> {
	client: Arc<C>,
	block_import: Arc<I>,
	env: Arc<E>,
	local_key: Arc<ed25519::Pair>,
	sync_oracle: SO,
	force_authoring: bool,
}

impl<H, B, C, E, I, Error, SO> SlotWorker<B> for AuraWorker<C, E, I, SO> where
	B: Block<Header=H>,
	C: ProvideRuntimeApi + ProvideCache<B> + AuxStore + Sync,
	C::Api: AuthoritiesApi<B>,
	E: Environment<B, Error=Error>,
	E::Proposer: Proposer<B, Error=Error>,
	<<E::Proposer as Proposer<B>>::Create as IntoFuture>::Future: Send + 'static,
	H: Header<
		Digest=generic::Digest<generic::DigestItem<B::Hash, ed25519::Public, ed25519::Signature>>,
		Hash=B::Hash,
	>,
	I: BlockImport<B> + Send + Sync + 'static,
	// P: Pair + Send + Sync + 'static,
	// ed25519::Public: PartialEq<<P as Pair>::Public> + AsRef<<P as Pair>::Public>,
	// ed25519::Signature: AsRef<<P as Pair>::Signature>,
	// P::Public: Member + Encode + Decode + Hash,
	// P::Signature: Member + Encode + Decode + Hash + Debug + Verify,
	// <<P as Pair>::Signature as Verify>::Signer: PartialEq + Encode + Decode + Clone,
	SO: SyncOracle + Send + Clone,
	// DigestItemFor<B>: CompatibleDigestItem + DigestItem<AuthorityId=ed25519::Public, Hash=B::Hash>,
	Error: ::std::error::Error + Send + From<::consensus_common::Error> + From<I::Error> + 'static,
{
	type OnSlot = Box<dyn Future<Item=(), Error=consensus_common::Error> + Send>;

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

		let authorities = match authorities::<B, C>(client.as_ref(), &BlockId::Hash(chain_head.hash())) {
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
		let maybe_author = slot_author(slot_num, &authorities);
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
					proposer.propose(
						slot_info.inherent_data,
						generic::Digest {
							logs: vec![
								<DigestItemFor<B>>::aura_pre_digest(slot_num),
							],
						},
						remaining_duration,
					).into_future(),
					remaining_duration,
				)
			} else {
				return Box::new(future::ok(()));
			}
		};

		Box::new(proposal_work.map(move |b| {
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
			let pre_digest: Result<u64, &str> = find_pre_digest::<H>(&header);
			if let Err(e) = pre_digest {
				error!(target: "aura", "FATAL ERROR: Invalid pre-digest: {}!", e);
				return
			} else {
				trace!(target: "aura", "Got correct number of seals.  Good!")
			};

			let header_num = header.number().clone();
			let parent_hash = header.parent_hash().clone();

			// sign the pre-sealed hash of the block and then
			// add it to a digest item.
			let header_hash = header.hash();
			let signature = pair.sign(header_hash.as_ref());
			let signature_digest_item = <DigestItemFor<B> as CompatibleDigestItem>::aura_seal(signature.clone());

			let import_block: ImportBlock<B> = ImportBlock {
				origin: BlockOrigin::Own,
				header,
				justification: None,
				post_digests: vec![signature_digest_item],
				body: Some(body),
				finalized: false,
				auxiliary: Vec::new(),
				fork_choice: ForkChoiceStrategy::LongestChain,
			};

			info!("Pre-sealed block for proposal at {}. Hash now {:?}, previously {:?}.",
					header_num,
					import_block.post_header().hash(),
					header_hash
			);
			telemetry!(CONSENSUS_INFO; "aura.pre_sealed_block";
				"header_num" => ?header_num,
				"hash_now" => ?import_block.post_header().hash(),
				"hash_previously" => ?header_hash
			);

			if let Err(e) = block_import.import_block(import_block, Default::default()) {
				warn!(target: "aura", "Error with block built on {:?}: {:?}",
						parent_hash, e);
				telemetry!(CONSENSUS_WARN; "aura.err_with_block_built_on";
					"hash" => ?parent_hash, "err" => ?e
				);
			}
		}).map_err(|e| consensus_common::Error::ClientImport(format!("{:?}", e)).into()))
	}
}

macro_rules! aura_err {
	($($i: expr),+) => {
		{ debug!(target: "aura", $($i),+)
		; format!($($i),+)
		}
	};
}

/// check a header has been signed by the right key. If the slot is too far in the future, an error will be returned.
/// if it's successful, returns the pre-header and the digest item containing the seal.
///
/// This digest item will always return `Some` when used with `as_aura_seal`.
fn check_header<C, B: Block, P: Pair, T>(
	client: &Arc<C>,
	transaction_pool: &Option<Arc<T>>,
	slot_now: u64,
	mut header: B::Header,
	hash: B::Hash,
	authorities: &[ed25519::Public],
) -> Result<CheckedHeader<B::Header, (u64, DigestItemFor<B>)>, String>
where
	T: PoolApi + SubmitReport<C, B>,
	<T as PoolApi>::Api: txpool::ChainApi<Block=B>,
	ed25519::Public: AsRef<<P as Pair>::Public>,
	// P::Signature: Encode + Decode + Clone + Verify<Signer = P::Public>,
	// P::Public: AsRef<P::Public> + Encode + Decode + PartialEq + Clone,
	DigestItemFor<B>: CompatibleDigestItem + DigestItem<Hash=B::Hash>,
	C: client::backend::AuxStore + client::blockchain::HeaderBackend<B> + ProvideRuntimeApi,
	C::Api: AuraApi<B>,
	// <<P as Pair>::Signature as Verify>::Signer: 
	// 	Encode + Decode + Clone + AsRef<<P as Pair>::Public> + PartialEq + Send + Sync,
{
	let seal = match header.digest_mut().pop() {
		Some(x) => x,
		None => return Err(format!("Header {:?} is unsealed", hash)),
	};
		
	let sig = seal.as_aura_seal().ok_or_else(|| {
		aura_err!("Header {:?} has a bad seal", hash)
	})?;

	let slot_num = find_pre_digest::<B::Header>(&header)?;

	if slot_num > slot_now {
		header.digest_mut().push(seal.clone());
		Ok(CheckedHeader::Deferred(header, slot_num))
	} else {
		// check the signature is valid under the expected authority and
		// chain state.
		let expected_author = match slot_author(slot_num, authorities) {
			None => return Err("Slot Author not found".to_string()),
			Some(author) => author,
		};

		let pre_hash = header.hash();

		if ed25519::Pair::verify(&sig, pre_hash.as_ref(), expected_author) {
			if let Some(equiv_proof) = check_equivocation::<
				_, _, AuraEquivProof<B::Header, ed25519::Signature>, ed25519::Signature,
			>(
				client.deref(),
				slot_now,
				slot_num,
				header.clone(),
				sig.clone(),
				expected_author.clone(),
			).map_err(|e| e.to_string())? {
				info!(
					"Slot author is equivocating at slot {} with headers {:?} and {:?}",
					slot_num,
					equiv_proof.first_header().hash(),
					equiv_proof.second_header().hash(),
				);
				let block_id = BlockId::number(client.info().best_number);
				transaction_pool.as_ref().map(|txpool|
					txpool.submit_report_call(
						client,
						client.runtime_api().construct_equiv_report_call(&block_id, equiv_proof).unwrap().as_slice(),
					)
				);
			} else {
					// transaction_pool.as_ref().map(|txpool|
					// 	submit_report_call(
					// 		client,
					// 		txpool,
					// 		Call::Aura(AuraCall::report_equivocation(
					// 			AuraEquivocationProof::new(
					// 				header.clone(),
					// 				header.clone(),
					// 				sig.clone(),
					// 				sig.clone(),
					// 			).encode()
					// 		)),
					// 	)
					// );
			}

			Ok(CheckedHeader::Checked(header, (slot_num, seal)))
		} else {
			Err(format!("Bad signature on {:?}", hash))
		}
	}
}

/// A verifier for Aura blocks.
pub struct AuraVerifier<C, E, P, T> {
	client: Arc<C>,
	transaction_pool: Option<Arc<T>>,
	extra: E,
	phantom: PhantomData<P>,
	inherent_data_providers: inherents::InherentDataProviders,
}

impl<C, E, P, T> AuraVerifier<C, E, P, T>
where
	T: PoolApi,
	<T as PoolApi>::Api: txpool::ChainApi,
	P: Send + Sync + 'static,
{
	fn check_inherents<B: Block>(
		&self,
		block: B,
		block_id: BlockId<B>,
		inherent_data: InherentData,
		timestamp_now: u64,
	) -> Result<(), String> 
	where
		C: ProvideRuntimeApi,
		C::Api: BlockBuilderApi<B> + AuraApi<B>,
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
impl<B: Block, C, E, P, T> Verifier<B> for AuraVerifier<C, E, P, T> where
	T: PoolApi + Send + Sync,
	<T as PoolApi>::Api: txpool::ChainApi<Block=B>,
	C: ProvideRuntimeApi + Send + Sync + client::backend::AuxStore + client::blockchain::HeaderBackend<B>,
	C::Api: BlockBuilderApi<B> + AuraApi<B>,
	P: Pair + Send + Sync + 'static,
	ed25519::Public: AsRef<<P as Pair>::Public>,
	// P::Public: Send + Sync + Hash + Eq + Clone + Decode + Encode + Debug + AsRef<P::Public> + 'static,
	// P::Signature: Encode + Decode + Clone + Verify<Signer = P::Public>,
	// <<P as Pair>::Signature as Verify>::Signer: Encode + Decode + Clone,
	DigestItemFor<B>: CompatibleDigestItem + DigestItem<AuthorityId=ed25519::Public>,
	E: ExtraVerification<B>,
	Self: Authorities<B>,
{
	fn verify(
		&self,
		origin: BlockOrigin,
		header: B::Header,
		justification: Option<Justification>,
		mut body: Option<Vec<B::Extrinsic>>,
	) -> Result<(ImportBlock<B>, Option<Vec<ed25519::Public>>), String> {
		let mut inherent_data = self.inherent_data_providers.create_inherent_data()
			.map_err(String::from)?;
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

		// We add one to allow for some small drift.
		// FIXME #1019 in the future, alter this queue to allow deferring of
		// headers.
		let checked_header = check_header::<C, B, P, T>(
			&self.client,
			&self.transaction_pool,
			slot_now + 1,
			header,
			hash,
			&authorities[..],
		)?;
		match checked_header {
			CheckedHeader::Checked(pre_header, (slot_num, seal)) => {
				// if the body is passed through, we need to use the runtime
				// to check that the internally-set timestamp in the inherents
				// actually matches the slot set in the seal.
				if let Some(inner_body) = body.take() {
					inherent_data.aura_replace_inherent_data(slot_num);
					let block = B::new(pre_header.clone(), inner_body);

					// skip the inherents verification if the runtime API is old.
					if self.client
						.runtime_api()
						.has_api_with::<dyn BlockBuilderApi<B>, _>(&BlockId::Hash(parent_hash), |v| v >= 2)
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
				telemetry!(
					CONSENSUS_TRACE;
					"aura.checked_and_importing";
					"pre_header" => ?pre_header
				);

				extra_verification.into_future().wait()?;

				let new_authorities = pre_header.digest()
					.log(DigestItem::as_authorities_change)
					.map(|digest| digest.to_vec());

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

				Ok((import_block, new_authorities))
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

impl<B, C, E, P, T> Authorities<B> for AuraVerifier<C, E, P, T> where
	B: Block,
	T: PoolApi + Send + Sync,
	<T as PoolApi>::Api: txpool::ChainApi<Block=B>,
	C: ProvideRuntimeApi + ProvideCache<B>,
	C::Api: AuthoritiesApi<B>,
{
	type Error = ConsensusError;

	fn authorities(&self, at: &BlockId<B>) -> Result<Vec<AuthorityIdFor<B>>, Self::Error> {
		authorities(self.client.as_ref(), at)
	}
}

fn initialize_authorities_cache<B, C>(client: &C) -> Result<(), ConsensusError> where
	B: Block,
	C: ProvideRuntimeApi + ProvideCache<B>,
	C::Api: AuthoritiesApi<B>,
{
	// no cache => no initialization
	let cache = match client.cache() {
		Some(cache) => cache,
		None => return Ok(()),
	};

	// check if we already have initialized the cache
	let genesis_id = BlockId::Number(Zero::zero());
	let genesis_authorities: Option<Vec<AuthorityIdFor<B>>> = cache
		.get_at(&well_known_cache_keys::AUTHORITIES, &genesis_id)
		.and_then(|v| Decode::decode(&mut &v[..]));
	if genesis_authorities.is_some() {
		return Ok(());
	}

	let map_err = |error| consensus_common::Error::from(consensus_common::Error::ClientImport(
		format!(
			"Error initializing authorities cache: {}",
			error,
		)));
	let genesis_authorities = authorities(client, &genesis_id)?;
	cache.initialize(&well_known_cache_keys::AUTHORITIES, genesis_authorities.encode())
		.map_err(map_err)?;

	Ok(())
}

#[allow(deprecated)]
fn authorities<B, C>(client: &C, at: &BlockId<B>) -> Result<Vec<AuthorityIdFor<B>>, ConsensusError> where
	B: Block,
	C: ProvideRuntimeApi + ProvideCache<B>,
	C::Api: AuthoritiesApi<B>,
{
	client
		.cache()
		.and_then(|cache| cache
			.get_at(&well_known_cache_keys::AUTHORITIES, at)
			.and_then(|v| Decode::decode(&mut &v[..]))
		)
		.or_else(|| AuthoritiesApi::authorities(&*client.runtime_api(), at).ok())
		.ok_or_else(|| consensus_common::Error::InvalidAuthoritiesSet.into())
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
			.map_err(Into::into)
			.map_err(consensus_common::Error::InherentData)
	} else {
		Ok(())
	}
}

/// Start an import queue for the Aura consensus algorithm.
pub fn import_queue<T, B, C, E, P>(
	slot_duration: SlotDuration,
	block_import: SharedBlockImport<B>,
	justification_import: Option<SharedJustificationImport<B>>,
	finality_proof_import: Option<SharedFinalityProofImport<B>>,
	finality_proof_request_builder: Option<SharedFinalityProofRequestBuilder<B>>,
	client: Arc<C>,
	extra: E,
	inherent_data_providers: InherentDataProviders,
	transaction_pool: Option<Arc<T>>,
) -> Result<AuraImportQueue<B>, consensus_common::Error> where
	B: Block,
	T: PoolApi + Send + Sync + 'static,
	<T as PoolApi>::Api: txpool::ChainApi<Block=B> + 'static,
	C: 'static + ProvideRuntimeApi + ProvideCache<B> + Send + Sync + AuxStore + client::blockchain::HeaderBackend<B>,
	C::Api: BlockBuilderApi<B> + AuthoritiesApi<B> + AuraApi<B>,
	P: Pair + Send + Sync + 'static,
	ed25519::Public: AsRef<<P as Pair>::Public>,
	// P::Public: Clone + Eq + Send + Sync + Hash + Debug + Encode + Decode + AsRef<P::Public>,
	// P::Signature: Encode + Decode + Clone + Verify<Signer = P::Public>,
	DigestItemFor<B>: CompatibleDigestItem + DigestItem<AuthorityId=ed25519::Public>,
	E: 'static + ExtraVerification<B>,
{
	register_aura_inherent_data_provider(&inherent_data_providers, slot_duration.get())?;
	initialize_authorities_cache(&*client)?;

	let verifier = Arc::new(
		AuraVerifier::<C, E, P, T> {
			client: client.clone(),
			transaction_pool: transaction_pool.clone(),
			extra,
			inherent_data_providers,
			phantom: PhantomData,
		}
	);
	Ok(BasicQueue::new(
		verifier,
		block_import,
		justification_import,
		finality_proof_import,
		finality_proof_request_builder,
	))
}

#[cfg(test)]
mod tests {
	use super::*;
	use futures::stream::Stream as _;
	use consensus_common::NoNetwork as DummyOracle;
	use network::test::*;
	use network::test::{Block as TestBlock, PeersClient, PeersFullClient};
	use network::config::ProtocolConfig;
	use parking_lot::Mutex;
	use tokio::runtime::current_thread;
	use keyring::sr25519::Keyring;
	use primitives::sr25519;
	use client::{LongestChain, BlockchainEvents};
	use test_client;
	use runtime_primitives::{
		traits::{Block as BlockT, DigestFor}, 
		transaction_validity::TransactionValidity,
	};
	use test_runtime::{Block, Extrinsic, Transfer, H256, AccountId};
	use transaction_pool::txpool::{Pool, PoolApi, ExtrinsicFor, BlockHash, error, NumberFor, ChainApi, ExHash};
	use test_client::AuthorityKeyring;

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

		fn propose(
			&self,
			_: InherentData,
			digests: DigestFor<TestBlock>,
			_: Duration,
		) -> Result<TestBlock, Error> {
			self.1.new_block(digests).unwrap().bake().map_err(|e| e.into())
		}
	}

	const SLOT_DURATION: u64 = 1;
	const TEST_ROUTING_INTERVAL: Duration = Duration::from_millis(50);

	pub struct AuraTestNet {
		peers: Vec<Arc<Peer<(), DummySpecialization>>>,
		started: bool,
	}

	#[derive(Debug, Default)]
	pub struct TestPool {}
	
	impl PoolApi for TestPool {
		type Api = TestPoolApi;
		fn submit_one(
			&self,
			_at: &BlockId<<Self::Api as ChainApi>::Block>,
			_xt: ExtrinsicFor<Self::Api>,
		) -> Result<ExHash<Self::Api>, <Self::Api as ChainApi>::Error> {
			Ok(ExHash::<Self::Api>::default())
		}
	}

	pub struct TestPoolApi {
		delay: Mutex<Option<std::sync::mpsc::Receiver<()>>>,
	}

	impl txpool::ChainApi for TestPoolApi {
		type Block = TestBlock;
		type Hash = u64;
		type Error = error::Error;

		fn validate_transaction(
			&self,
			at: &BlockId<Self::Block>,
			uxt: ExtrinsicFor<Self>,
		) -> Result<TransactionValidity, Self::Error> {

			let block_number = self.block_id_to_number(at)?.unwrap();
			let nonce = uxt.transfer().nonce;

			// This is used to control the test flow.
			if nonce > 0 {
				let opt = self.delay.lock().take();
				if let Some(delay) = opt {
					if delay.recv().is_err() {
						println!("Error waiting for delay!");
					}
				}
			}

			if nonce < block_number {
				Ok(TransactionValidity::Invalid(0))
			} else {
				Ok(TransactionValidity::Valid {
					priority: 4,
					requires: if nonce > block_number { vec![vec![nonce as u8 - 1]] } else { vec![] },
					provides: vec![vec![nonce as u8]],
					longevity: 3,
					propagate: true,
				})
			}
		}

		/// Returns a block number given the block id.
		fn block_id_to_number(&self, at: &BlockId<Self::Block>) -> Result<Option<NumberFor<Self>>, Self::Error> {
			Ok(match at {
				BlockId::Number(num) => Some(*num),
				BlockId::Hash(_) => None,
			})
		}

		/// Returns a block hash given the block id.
		fn block_id_to_hash(&self, at: &BlockId<Self::Block>) -> Result<Option<BlockHash<Self>>, Self::Error> {
			Ok(match at {
				BlockId::Number(num) => Some(H256::from_low_u64_be(*num)).into(),
				BlockId::Hash(_) => None,
			})
		}

		/// Hash the extrinsic.
		fn hash_and_length(&self, uxt: &ExtrinsicFor<Self>) -> (Self::Hash, usize) {
			let len = uxt.encode().len();
			(
				(H256::from(uxt.transfer().from.clone()).to_low_u64_be() << 5) + uxt.transfer().nonce,
				len
			)
		}
	}

	impl TestNetFactory for AuraTestNet {
		type Specialization = DummySpecialization;
		type Verifier = AuraVerifier<PeersFullClient, NothingExtra, sr25519::Pair, TestPool>;
		type PeerData = ();

		/// Create new test network with peers and given config.
		fn from_config(_config: &ProtocolConfig) -> Self {
			AuraTestNet {
				peers: Vec::new(),
				started: false,
			}
		}

		fn make_verifier(&self, client: PeersClient, _cfg: &ProtocolConfig)
			-> Arc<Self::Verifier>
		{
			match client {
				PeersClient::Full(client) => {
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
						transaction_pool: None,
						extra: NothingExtra,
						inherent_data_providers,
						phantom: Default::default(),
					})
				},
				PeersClient::Light(_) => unreachable!("No (yet) tests for light client + Aura"),
			}
		}

		fn uses_tokio(&self) -> bool {
			true
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
	#[allow(deprecated)]
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
			let client = net.lock().peer(*peer_id).client().as_full().expect("full clients are created").clone();
			#[allow(deprecated)]
			let select_chain = LongestChain::new(
				client.backend().clone(),
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
				inherent_data_providers,
				false,
			).expect("Starts aura");

			runtime.spawn(aura);
		}

		// wait for all finalized on each.
		let wait_for = ::futures::future::join_all(import_notifications)
			.map(|_| ())
			.map_err(|_| ());

		let drive_to_completion = ::tokio_timer::Interval::new_interval(TEST_ROUTING_INTERVAL)
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

		assert_eq!(client.info().chain.best_number, 0);
		assert_eq!(authorities(&client, &BlockId::Number(0)).unwrap(), vec![
			Keyring::Alice.into(),
			Keyring::Bob.into(),
			Keyring::Charlie.into()
		]);
	}
}
