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

//! BABE (Blind Assignment for Blockchain Extension) consensus in substrate.
//!
//! Note that 1 second slot time is optimal.
#![forbid(warnings, unsafe_code, missing_docs)]
extern crate core;
pub use babe_primitives::*;
use runtime_primitives::{generic, generic::BlockId, Justification};
use runtime_primitives::traits::{
	Block, Header, Digest, DigestItemFor, DigestItem, ProvideRuntimeApi, AuthorityIdFor,
};
use std::{
	sync::Arc,
	time::Duration,
	thread,
	hash::Hash,
	fmt::Debug,
	u64,
};
use parity_codec::{Decode, Encode, Input};
use primitives::{
	crypto::Pair,
	sr25519::{Public, Signature, LocalizedSignature, self},
};
use merlin::Transcript;
use inherents::{InherentDataProviders, InherentData, RuntimeString};
use substrate_telemetry::{telemetry, CONSENSUS_TRACE, CONSENSUS_DEBUG, CONSENSUS_WARN, CONSENSUS_INFO};
use schnorrkel::{
	SecretKey as Secret,
	context::SigningTranscript,
	keys::Keypair,
	vrf::{
		VRFProof, VRFProofBatchable, VRFInOut, VRFOutput,
		VRF_OUTPUT_LENGTH,
	},
	PUBLIC_KEY_LENGTH, SIGNATURE_LENGTH,
};
pub use consensus_common::SyncOracle;
use authorities::AuthoritiesApi;
use consensus_common::{self, Authorities, BlockImport, Environment, Proposer,
	ForkChoiceStrategy, ImportBlock, BlockOrigin, Error as ConsensusError,
};
use srml_babe::{
	InherentType as BabeInherent, BabeInherentData,
	timestamp::{TimestampInherentData, InherentType as TimestampInherent, InherentError as TIError}
};
use consensus_common::well_known_cache_keys;
use consensus_common::import_queue::{Verifier, BasicQueue, SharedBlockImport, SharedJustificationImport};
use client::{
	ChainHead,
	block_builder::api::BlockBuilder as BlockBuilderApi,
	blockchain::ProvideCache,
	runtime_api::ApiExt,
	error::Result as CResult,
	backend::AuxStore,
};
use slots::CheckedHeader;

use futures::{Future, IntoFuture, future};
use tokio::timer::Timeout;
use log::{warn, debug, info, trace};

use slots::{SlotData, SlotWorker, SlotInfo, SlotCompatible, slot_now};
use rand::Rng;

/// A BABE seal.  It includes:
/// 
/// * The public key
/// * The VRF proof
/// * The signature
/// * The slot number
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BabeSeal {
	proof: VRFProof,
	vrf_output: VRFOutput,
	signature: LocalizedSignature,
	slot_num: u64,
}

impl Encode for BabeSeal {
	fn encode(&self) -> Vec<u8> {
		parity_codec::Encode::encode(&(
			self.proof.to_bytes(),
			self.vrf_output.as_bytes(),
			self.signature.signature.0,
			self.signature.signer.0,
			self.slot_num,
		))
	}
}

impl Decode for BabeSeal {
	fn decode<R: Input>(i: &mut R) -> Option<Self> {
		let (public_key, proof, output, sig, slot_num): (
			[u8; PUBLIC_KEY_LENGTH],
			[u8; PUBLIC_KEY_LENGTH],
			[u8; VRF_OUTPUT_LENGTH],
			[u8; SIGNATURE_LENGTH],
			u64,
		) = Decode::decode(i)?;
		Some(BabeSeal {
			proof: VRFProof::from_bytes(&proof).ok()?,
			vrf_output: VRFOutput::from_bytes(&output).ok()?,
			signature: LocalizedSignature {
				signature: Signature(sig),
				signer: Public(public_key),
			},
			slot_num,
		})
	}
}

/// A slot duration. Create with `get_or_compute`.
// FIXME: Once Rust has higher-kinded types, the duplication between this
// and `super::babe::SlotDuration` can be eliminated.
pub struct SlotDuration(slots::SlotDuration<BabeConfiguration>);

impl SlotDuration {
	/// Either fetch the slot duration from disk or compute it from the genesis
	/// state.
	pub fn get_or_compute<B: Block, C>(client: &C) -> CResult<Self>
	where
		C: AuxStore, C: ProvideRuntimeApi, C::Api: BabeApi<B>,
	{
		slots::SlotDuration::get_or_compute(client, |a, b| a.startup_data(b)).map(Self)
	}

	/// Get the slot duration in milliseconds.
	pub fn get(&self) -> u64 {
		self.0.slot_duration()
	}
}

fn inherent_to_common_error(err: RuntimeString) -> consensus_common::Error {
	consensus_common::ErrorKind::InherentData(err.into()).into()
}

/// A digest item which is usable with BABE consensus.
pub trait CompatibleDigestItem: Sized {
	/// Construct a digest item which contains a slot number and a signature on the
	/// hash.
	fn babe_seal(signature: BabeSeal) -> Self;

	/// If this item is an Babe seal, return the slot number and signature.
	fn as_babe_seal(&self) -> Option<BabeSeal>;
}

impl<Hash> CompatibleDigestItem for generic::DigestItem<Hash, Public, Secret> {
	/// Construct a digest item which is aaAASSAAAAAASDC   a slot number and a signature on the
	/// hash.
	fn babe_seal(signature: BabeSeal) -> Self {
		generic::DigestItem::Consensus(BABE_ENGINE_ID, signature.encode())
	}

	/// If this item is an BABE seal, return the slot number and signature.
	fn as_babe_seal(&self) -> Option<BabeSeal> {
		match self {
			generic::DigestItem::Consensus(BABE_ENGINE_ID, seal) => Decode::decode(&mut &seal[..]),
			_ => None,
		}
	}
}

struct BabeSlotCompatible;

impl SlotCompatible for BabeSlotCompatible {
	fn extract_timestamp_and_slot(
		data: &InherentData
	) -> Result<(TimestampInherent, u64), consensus_common::Error> {
		data.timestamp_inherent_data()
			.and_then(|t| data.babe_inherent_data().map(|a| (t, a.slot_duration)))
			.map_err(slots::inherent_to_common_error)
	}
}

/// Start the babe worker in a separate thread.
pub fn start_babe_thread<B, C, E, I, SO, Error, OnExit>(
	slot_duration: SlotDuration,
	local_key: Arc<sr25519::Pair>,
	client: Arc<C>,
	block_import: Arc<I>,
	env: Arc<E>,
	sync_oracle: SO,
	on_exit: OnExit,
	inherent_data_providers: InherentDataProviders,
	force_authoring: bool,
) -> Result<(), consensus_common::Error> where
	B: Block + 'static,
	C: ChainHead<B> + ProvideRuntimeApi + ProvideCache<B> + Send + Sync + 'static,
	C::Api: AuthoritiesApi<B>,
	E: Environment<B, Error=Error> + Send + Sync + 'static,
	E::Proposer: Proposer<B, Error=Error> + Send + 'static,
	<<E::Proposer as Proposer<B>>::Create as IntoFuture>::Future: Send + 'static,
	I: BlockImport<B> + Send + Sync + 'static,
	Error: From<I::Error> + 'static,
	SO: SyncOracle + Send + Sync + Clone + 'static,
	OnExit: Future<Item=(), Error=()> + Send + 'static,
	DigestItemFor<B>: CompatibleDigestItem + DigestItem<AuthorityId=Public> + 'static,
	Error: ::std::error::Error + Send + From<::consensus_common::Error> + 'static,
{
	let worker = BabeWorker {
		client: client.clone(),
		block_import,
		env,
		local_key,
		inherent_data_providers: inherent_data_providers.clone(),
		sync_oracle: sync_oracle.clone(),
		force_authoring,
	};

	slots::start_slot_worker_thread::<_, _, _, _, BabeSlotCompatible, BabeConfiguration, _>(
		slot_duration.0,
		client,
		Arc::new(worker),
		sync_oracle,
		on_exit,
		inherent_data_providers
	)
}

/// Start the babe worker. The returned future should be run in a tokio runtime.
pub fn start_babe<B, C, E, I, SO, Error, OnExit>(
	slot_duration: SlotDuration,
	local_key: Arc<sr25519::Pair>,
	client: Arc<C>,
	block_import: Arc<I>,
	env: Arc<E>,
	sync_oracle: SO,
	on_exit: OnExit,
	inherent_data_providers: InherentDataProviders,
	force_authoring: bool,
) -> Result<impl Future<Item=(), Error=()>, consensus_common::Error> where
	B: Block,
	C: ChainHead<B> + ProvideRuntimeApi + ProvideCache<B>,
	C::Api: AuthoritiesApi<B>,
	E: Environment<B, Error=Error>,
	E::Proposer: Proposer<B, Error=Error>,
	<<E::Proposer as Proposer<B>>::Create as IntoFuture>::Future: Send + 'static,
	I: BlockImport<B> + Send + Sync + 'static,
	SO: SyncOracle + Send + Sync + Clone,
	DigestItemFor<B>: CompatibleDigestItem + DigestItem<AuthorityId=Public>,
	Error: ::std::error::Error + Send + From<::consensus_common::Error> + From<I::Error> + 'static,
	OnExit: Future<Item=(), Error=()>,
{
	let worker = BabeWorker {
		client: client.clone(),
		block_import,
		env,
		local_key,
		inherent_data_providers: inherent_data_providers.clone(),
		sync_oracle: sync_oracle.clone(),
		force_authoring,
	};
	slots::start_slot_worker::<_, _, _, _, _, BabeSlotCompatible, _>(
		slot_duration.0,
		client,
		Arc::new(worker),
		sync_oracle,
		on_exit,
		inherent_data_providers
	)
}

struct BabeWorker<C, E, I, SO> {
	client: Arc<C>,
	block_import: Arc<I>,
	env: Arc<E>,
	local_key: Arc<sr25519::Pair>,
	sync_oracle: SO,
	inherent_data_providers: InherentDataProviders,
	force_authoring: bool,
}

impl<B: Block, C, E, I, Error, SO> SlotWorker<B> for BabeWorker<C, E, I, SO> where
	C: ProvideRuntimeApi + ProvideCache<B>,
	C::Api: AuthoritiesApi<B>,
	E: Environment<B, Error=Error>,
	E::Proposer: Proposer<B, Error=Error>,
	<<E::Proposer as Proposer<B>>::Create as IntoFuture>::Future: Send + 'static,
	I: BlockImport<B> + Send + Sync + 'static,
	SO: SyncOracle + Send + Clone,
	DigestItemFor<B>: CompatibleDigestItem + DigestItem<AuthorityId=Public>,
	Error: std::error::Error + Send + From<::consensus_common::Error> + From<I::Error> + 'static,
{
	type OnSlot = Box<Future<Item=(), Error=consensus_common::Error> + Send>;

	fn on_start(
		&self,
		slot_duration: u64
	) -> Result<(), consensus_common::Error> {
		register_babe_inherent_data_provider(&self.inherent_data_providers, slot_duration)
	}

	fn on_slot(
		&self,
		chain_head: B::Header,
		slot_info: SlotInfo,
	) -> Self::OnSlot {
		let pair = self.local_key.clone();
		let _public_key = self.local_key.public();
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
				telemetry!(CONSENSUS_WARN; "babe.unable_fetching_authorities";
					"slot" => ?chain_head.hash(), "err" => ?e
				);
				return Box::new(future::ok(()));
			}
		};

		if !self.force_authoring && self.sync_oracle.is_offline() && authorities.len() > 1 {
			debug!(target: "babe", "Skipping proposal slot. Waiting for the network.");
			telemetry!(CONSENSUS_DEBUG; "babe.skipping_proposal_slot";
				"authorities_len" => authorities.len()
			);
			return Box::new(future::ok(()));
		}

		// FIXME replace the dummy empty slices with real data
		let (proposal_work, vrf_output, proof) = if let Some((inout, proof, _batchable_proof)) = author_block(
			&[0u8; 0], slot_info.number, &[0u8; 0],	0, &authorities, &pair, u64::MAX / 4) {
			debug!(
				target: "babe", "Starting authorship at slot {}; timestamp = {}",
				slot_num,
				timestamp
			);
			telemetry!(CONSENSUS_DEBUG; "babe.starting_authorship";
				"slot_num" => slot_num, "timestamp" => timestamp
			);

			// we are the slot author. make a block and sign it.
			let proposer = match env.init(&chain_head, &authorities) {
				Ok(p) => p,
				Err(e) => {
					warn!("Unable to author block in slot {:?}: {:?}", slot_num, e);
					telemetry!(CONSENSUS_WARN; "babe.unable_authoring_block";
						"slot" => slot_num, "err" => ?e
					);
					return Box::new(future::ok(()))
				}
			};

			let remaining_duration = slot_info.remaining_duration();
			// deadline our production to approx. the end of the
			// slot
			(Timeout::new(
				proposer.propose(slot_info.inherent_data, remaining_duration).into_future(),
				remaining_duration,
			), inout.to_output(), proof)
		} else {
			return Box::new(future::ok(()));
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
						telemetry!(CONSENSUS_INFO; "babe.discarding_proposal_took_too_long";
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
					let to_sign = (slot_num, pre_hash, proof.to_bytes()).encode();
					let signature = pair.sign(&to_sign[..]);
					let item = <DigestItemFor<B> as CompatibleDigestItem>::babe_seal(BabeSeal {
						proof,
						signature: LocalizedSignature {
							signature,
							signer: pair.public(),
						},
						slot_num,
						vrf_output,
					});

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
					telemetry!(CONSENSUS_INFO; "babe.pre_sealed_block";
						"header_num" => ?header_num,
						"hash_now" => ?import_block.post_header().hash(),
						"hash_previously" => ?pre_hash
					);

					if let Err(e) = block_import.import_block(import_block, Default::default()) {
						warn!(target: "babe", "Error with block built on {:?}: {:?}",
							  parent_hash, e);
						telemetry!(CONSENSUS_WARN; "babe.err_with_block_built_on";
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
/// This digest item will always return `Some` when used with `as_babe_seal`.
//
// FIXME #1018 needs misbehavior types
#[forbid(warnings)]
fn check_header<B: Block + Sized>(
	slot_now: u64,
	mut header: B::Header,
	hash: B::Hash,
	authorities: &[Public],
) -> Result<CheckedHeader<B::Header, DigestItemFor<B>>, String>
	where DigestItemFor<B>: CompatibleDigestItem,
{
	let digest_item = match header.digest_mut().pop() {
		Some(x) => x,
		None => return Err(format!("Header {:?} is unsealed", hash)),
	};

	let BabeSeal { slot_num, signature: LocalizedSignature { signer, signature }, proof, vrf_output } = digest_item.as_babe_seal().ok_or_else(|| {
		debug!(target: "babe", "Header {:?} is unsealed", hash);
		format!("Header {:?} is unsealed", hash)
	})?;
	// FIXME!!
	let threshold = u64::MAX / 4;
	if slot_num > slot_now {
		header.digest_mut().push(digest_item);
		Ok(CheckedHeader::Deferred(header, slot_num))
	} else if !authorities.contains(&signer) {
		Err("Slot Author not found".to_string())
	} else {
		let pre_hash = header.hash();
		let to_sign = (slot_num, pre_hash).encode();

		if sr25519::Pair::verify(&signature, &to_sign[..], &signer) {
			let (inout, _batchable_proof) = {
				let transcript = make_transcript(
					Default::default(),
					slot_num,
					Default::default(),
					0,
				);
				schnorrkel::PublicKey::from_bytes(signer.as_slice()).and_then(|p| p.vrf_verify(transcript, &vrf_output, &proof)).map_err(|s| {
					debug!(target: "babe", "VRF verification failed: {:?}", s);
					format!("VRF verification failed")
				})?
			};
			let r: u64 = inout.make_chacharng(b"substrate-babe-vrf").gen();
			if r < threshold {
				Ok(CheckedHeader::Checked(header, digest_item))
			} else {
				Err(format!("Validator {:?} made seal when it wasn’t its turn", signer))
			}
		} else {
			Err(format!("Bad signature on {:?}", hash))
		}
	}
}

/// Extra verification for Babe blocks.
pub trait ExtraVerification<B: Block>: Send + Sync {
	/// Future that resolves when the block is verified or fails with error if not.
	type Verified: IntoFuture<Item=(),Error=String>;

	/// Do additional verification for this block.
	fn verify(
		&self,
		header: &B::Header,
		body: Option<&[B::Extrinsic]>,
	) -> Self::Verified;
}

/// A verifier for Babe blocks.
pub struct BabeVerifier<C, E> {
	client: Arc<C>,
	extra: E,
	inherent_data_providers: inherents::InherentDataProviders,
}

impl<C, E> BabeVerifier<C, E> {
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
							target: "babe",
							"halting for block {} seconds in the future",
							diff
						);
						telemetry!(CONSENSUS_INFO; "babe.halting_for_future_block";
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

impl<B, C, E> Authorities<B> for BabeVerifier<C, E> where
	B: Block,
	C: ProvideRuntimeApi + ProvideCache<B>,
	C::Api: AuthoritiesApi<B>,
{
	type Error = ConsensusError;

	fn authorities(&self, at: &BlockId<B>) -> Result<Vec<AuthorityIdFor<B>>, Self::Error> {
		authorities(self.client.as_ref(), at)
	}
}

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
				panic!("We don’t support deprecated code with new consensus algorithms, therefore this is unreachable; qed")
			}
		}).ok_or_else(|| consensus_common::ErrorKind::InvalidAuthoritiesSet.into())
}

/// The BABE import queue type.
pub type BabeImportQueue<B> = BasicQueue<B>;

/// Register the babe inherent data provider, if not registered already.
fn register_babe_inherent_data_provider(
	inherent_data_providers: &InherentDataProviders,
	slot_duration: u64,
) -> Result<(), consensus_common::Error> {
	if !inherent_data_providers.has_provider(&srml_babe::INHERENT_IDENTIFIER) {
		inherent_data_providers
			.register_provider(srml_babe::InherentDataProvider::new(slot_duration))
			.map_err(inherent_to_common_error)
	} else {
		Ok(())
	}
}

fn get_keypair(q: &sr25519::Pair) -> &Keypair {
	q.as_ref()
}

/// Pieces:
/// 
/// 1. VRF winnership
/// 2. * VRF randomness
///    * relative time

fn make_transcript(
	randomness: &[u8],
	slot_number: u64,
	genesis_hash: &[u8],
	epoch: u64,
) -> Transcript {
	let mut transcript = Transcript::new(&BABE_ENGINE_ID);
	transcript.proto_name(&BABE_ENGINE_ID);
	transcript.commit_bytes(b"slot number", &slot_number.to_le_bytes());
	transcript.commit_bytes(b"genesis block hash", genesis_hash);
	transcript.commit_bytes(b"current epoch", &epoch.to_le_bytes());
	transcript.commit_bytes(b"chain randomness", randomness);
	transcript
}

/// Hash into chain:
/// 
/// * slot number
/// * epoch
/// * genesis hash
/// * chain randomness
fn author_block(
	randomness: &[u8],
	slot_number: u64,
	genesis_hash: &[u8],
	epoch: u64,
	authorities: &[sr25519::Public],
	key: &sr25519::Pair,
	threshold: u64,
) -> Option<(VRFInOut, VRFProof, VRFProofBatchable)> {
	// FIXME this is O(n)
	if !authorities.contains(&key.public()) { return None }
	let (inout, proof, batchable_proof) = {
		let transcript = make_transcript(
			randomness,
			slot_number,
			genesis_hash,
			epoch,
		);
		get_keypair(key).vrf_sign(transcript)
	};
	let r: u64 = inout.make_chacharng(b"substrate-babe-vrf").gen();
	if r < threshold {
		Some((inout, proof, batchable_proof))
	} else {
		None
	}
}

impl<B: Block, C, E> Verifier<B> for BabeVerifier<C, E> where
	C: ProvideRuntimeApi + Send + Sync,
	C::Api: BlockBuilderApi<B>,
	DigestItemFor<B>: CompatibleDigestItem + DigestItem<AuthorityId=Public>,
	E: ExtraVerification<B>,
	Self: Authorities<B>,
{
	fn verify(
		&self,
		origin: BlockOrigin,
		header: B::Header,
		justification: Option<Justification>,
		mut body: Option<Vec<B::Extrinsic>>,
	) -> Result<(ImportBlock<B>, Option<Vec<Public>>), String> {
		let mut inherent_data = self.inherent_data_providers.create_inherent_data().map_err(String::from)?;
		let (timestamp_now, slot_now) = BabeSlotCompatible::extract_timestamp_and_slot(&inherent_data)
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
		let checked_header = check_header::<B>(
			slot_now + 1,
			header,
			hash,
			&authorities[..],
		)?;
		match checked_header {
			CheckedHeader::Checked(pre_header, seal) => {
				let BabeSeal { slot_num, .. } = seal.as_babe_seal()
					.expect("check_header always returns a seal digest item; qed");

				// if the body is passed through, we need to use the runtime
				// to check that the internally-set timestamp in the inherents
				// actually matches the slot set in the seal.
				if let Some(inner_body) = body.take() {
					inherent_data.babe_replace_inherent_data(BabeInherent {
						slot_num,
						slot_duration: 0,
					});
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

				trace!(target: "babe", "Checked {:?}; importing.", pre_header);
				telemetry!(CONSENSUS_TRACE; "babe.checked_and_importing"; "pre_header" => ?pre_header);

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
				debug!(target: "babe", "Checking {:?} failed; {:?}, {:?}.", hash, a, b);
				telemetry!(CONSENSUS_DEBUG; "babe.header_too_far_in_future";
					"hash" => ?hash, "a" => ?a, "b" => ?b
				);
				Err(format!("Header {:?} rejected: too far in the future", hash))
			}
		}
	}
}

/// Start an import queue for the Babe consensus algorithm.
pub fn import_queue<B, C, E, P>(
	slot_duration: SlotDuration,
	block_import: SharedBlockImport<B>,
	justification_import: Option<SharedJustificationImport<B>>,
	client: Arc<C>,
	extra: E,
	inherent_data_providers: InherentDataProviders,
) -> Result<BabeImportQueue<B>, consensus_common::Error> where
	B: Block,
	C: 'static + ProvideRuntimeApi + ProvideCache<B> + Send + Sync,
	C::Api: BlockBuilderApi<B> + AuthoritiesApi<B>,
	DigestItemFor<B>: CompatibleDigestItem + DigestItem<AuthorityId=Public>,
	E: 'static + ExtraVerification<B>,
	P: Pair + Send + Sync + 'static,
	P::Public: Clone + Eq + Send + Sync + Hash + Debug + Encode + Decode + AsRef<P::Public>,
	P::Signature: Encode + Decode,
{
	register_babe_inherent_data_provider(&inherent_data_providers, slot_duration.get())?;

	let verifier = Arc::new(
		BabeVerifier {
			client: client.clone(),
			extra,
			inherent_data_providers,
		}
	);
	Ok(BasicQueue::new(verifier, block_import, justification_import))
}
