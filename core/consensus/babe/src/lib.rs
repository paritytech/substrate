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
//! BABE (Blind Assignment for Blockchain Extension) consensus in substrate.
//!
//! # Stability
//!
//! This crate is highly unstable and experimental.  Breaking changes may
//! happen at any point.  This crate is also missing features, such as banning
//! of malicious validators, that are essential for a production network.
#![forbid(unsafe_code, missing_docs)]
#![deny(warnings)]
extern crate core;
pub use babe_primitives::*;
pub use consensus_common::SyncOracle;
use consensus_common::ExtraVerification;
use runtime_primitives::{generic, generic::BlockId, Justification};
use runtime_primitives::traits::{
	Block, Header, Digest, DigestItemFor, DigestItem, ProvideRuntimeApi, AuthorityIdFor,
};
use std::{sync::Arc, u64, fmt::Debug};
use parity_codec::{Decode, Encode, Input};
use primitives::{
	crypto::Pair,
	sr25519::{Public, Signature, LocalizedSignature, self},
};
use merlin::Transcript;
use inherents::{InherentDataProviders, InherentData, RuntimeString};
use substrate_telemetry::{telemetry, CONSENSUS_TRACE, CONSENSUS_DEBUG, CONSENSUS_WARN, CONSENSUS_INFO};
use schnorrkel::{
	keys::Keypair,
	vrf::{
		VRFProof, VRFProofBatchable, VRFInOut, VRFOutput,
		VRF_OUTPUT_LENGTH, VRF_PROOF_LENGTH,
	},
	PUBLIC_KEY_LENGTH, SIGNATURE_LENGTH,
};
use authorities::AuthoritiesApi;
use consensus_common::{self, Authorities, BlockImport, Environment, Proposer,
	ForkChoiceStrategy, ImportBlock, BlockOrigin, Error as ConsensusError,
};
use srml_babe::{
	BabeInherentData,
	timestamp::{TimestampInherentData, InherentType as TimestampInherent}
};
use consensus_common::{SelectChain, well_known_cache_keys};
use consensus_common::import_queue::{Verifier, BasicQueue};
use client::{
	block_builder::api::BlockBuilder as BlockBuilderApi,
	blockchain::ProvideCache,
	runtime_api::ApiExt,
	error::Result as CResult,
	backend::AuxStore,
};
use slots::CheckedHeader;
use futures::{Future, IntoFuture, future};
use tokio::timer::Timeout;
use log::{error, warn, debug, info, trace};

use slots::{SlotWorker, SlotInfo, SlotCompatible, slot_now};

/// A BABE seal.  It includes:
///
/// * The public key
/// * The VRF proof
/// * The signature
/// * The slot number
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BabeSeal {
	vrf_output: VRFOutput,
	proof: VRFProof,
	signature: LocalizedSignature,
	slot_num: u64,
}

/// The prefix used by BABE for its VRF keys.
pub const BABE_VRF_PREFIX: &'static [u8] = b"substrate-babe-vrf";

macro_rules! babe_assert_eq {
	($a: expr, $b: expr) => {
		{
			let ref a = $a;
			let ref b = $b;
			if a != b {
				error!(
					target: "babe",
					"Expected {:?} to equal {:?}, but they were not",
					stringify!($a),
					stringify!($b),
				);
				assert_eq!(a, b);
			}
		}
	};
}

type TmpDecode = (
	[u8; VRF_OUTPUT_LENGTH],
	[u8; VRF_PROOF_LENGTH],
	[u8; SIGNATURE_LENGTH],
	[u8; PUBLIC_KEY_LENGTH],
	u64,
);

impl Encode for BabeSeal {
	fn encode(&self) -> Vec<u8> {
		let tmp: TmpDecode = (
			*self.vrf_output.as_bytes(),
			self.proof.to_bytes(),
			self.signature.signature.0,
			self.signature.signer.0,
			self.slot_num,
		);
		let encoded = parity_codec::Encode::encode(&tmp);
		if cfg!(any(test, debug_assertions)) {
			debug!(target: "babe", "Checking if encoding was correct");
			let decoded_version = Self::decode(&mut &encoded[..])
				.expect("we just encoded this ourselves, so it is correct; qed");
			babe_assert_eq!(decoded_version.proof, self.proof);
			babe_assert_eq!(decoded_version.vrf_output, self.vrf_output);
			babe_assert_eq!(decoded_version.signature.signature, self.signature.signature);
			babe_assert_eq!(decoded_version.signature.signer, self.signature.signer);
			babe_assert_eq!(decoded_version.slot_num, self.slot_num);
			debug!(target: "babe", "Encoding was correct")
		}
		encoded
	}
}

impl Decode for BabeSeal {
	fn decode<R: Input>(i: &mut R) -> Option<Self> {
		let (output, proof, sig, public_key, slot_num): TmpDecode = Decode::decode(i)?;
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
// and `super::aura::Config` can be eliminated.
// https://github.com/paritytech/substrate/issues/2434
pub struct Config(slots::SlotDuration<BabeConfiguration>);

impl Config {
	/// Either fetch the slot duration from disk or compute it from the genesis
	/// state.
	pub fn get_or_compute<B: Block, C>(client: &C) -> CResult<Self>
	where
		C: AuxStore, C: ProvideRuntimeApi, C::Api: BabeApi<B>,
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

fn inherent_to_common_error(err: RuntimeString) -> consensus_common::Error {
	consensus_common::ErrorKind::InherentData(err.into()).into()
}

/// A digest item which is usable with BABE consensus.
pub trait CompatibleDigestItem: Sized {
	/// Construct a digest item which contains a slot number and a signature
	/// on the hash.
	fn babe_seal(signature: BabeSeal) -> Self;

	/// If this item is an Babe seal, return the slot number and signature.
	fn as_babe_seal(&self) -> Option<BabeSeal>;
}

impl<T, Hash> CompatibleDigestItem for generic::DigestItem<Hash, Public, T>
	where T: Debug, Hash: Debug
{
	/// Construct a digest item which contains a slot number and a signature
	/// on the hash.
	fn babe_seal(signature: BabeSeal) -> Self {
		generic::DigestItem::Consensus(BABE_ENGINE_ID, signature.encode())
	}

	/// If this item is an BABE seal, return the slot number and signature.
	fn as_babe_seal(&self) -> Option<BabeSeal> {
		match self {
			generic::DigestItem::Consensus(BABE_ENGINE_ID, seal) => {
				match Decode::decode(&mut &seal[..]) {
					s @ Some(_) => s,
					s @ None => {
						info!(target: "babe", "Failed to decode {:?}", seal);
						s
					}
				}
			}
			_ => {
				info!(target: "babe", "Invalid consensus: {:?}!", self);
				None
			}
		}
	}
}

struct BabeSlotCompatible;

impl SlotCompatible for BabeSlotCompatible {
	fn extract_timestamp_and_slot(
		data: &InherentData
	) -> Result<(TimestampInherent, u64), consensus_common::Error> {
		trace!(target: "babe", "extract timestamp");
		data.timestamp_inherent_data()
			.and_then(|t| data.babe_inherent_data().map(|a| (t, a)))
			.map_err(slots::inherent_to_common_error)
	}
}

/// Parameters for BABE.
pub struct BabeParams<C, E, I, SO, SC, OnExit> {

	/// The configuration for BABE.  Includes the slot duration, threshold, and
	/// other parameters.
	pub config: Config,

	/// The key of the node we are running on.
	pub local_key: Arc<sr25519::Pair>,

	/// The client to use
	pub client: Arc<C>,

	/// The SelectChain Strategy
	pub select_chain: SC,

	/// A block importer
	pub block_import: Arc<I>,

	/// The environment
	pub env: Arc<E>,

	/// A sync oracle
	pub sync_oracle: SO,

	/// Exit callback.
	pub on_exit: OnExit,

	/// Providers for inherent data.
	pub inherent_data_providers: InherentDataProviders,

	/// Force authoring of blocks even if we are offline
	pub force_authoring: bool,
}

/// Start the babe worker. The returned future should be run in a tokio runtime.
pub fn start_babe<B, C, E, I, SO, SC, Error, OnExit>(BabeParams {
	config,
	local_key,
	client,
	select_chain,
	block_import,
	env,
	sync_oracle,
	on_exit,
	inherent_data_providers,
	force_authoring,
}: BabeParams<C, E, I, SO, SC, OnExit>) -> Result<
	impl Future<Item=(), Error=()>,
	consensus_common::Error,
> where
	B: Block,
	C: ProvideRuntimeApi + ProvideCache<B>,
	C::Api: AuthoritiesApi<B>,
	E: Environment<B, Error=Error>,
	E::Proposer: Proposer<B, Error=Error>,
	<<E::Proposer as Proposer<B>>::Create as IntoFuture>::Future: Send + 'static,
	I: BlockImport<B> + Send + Sync + 'static,
	SO: SyncOracle + Send + Sync + Clone,
	SC: SelectChain<B>,
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
		threshold: config.threshold(),
	};
	slots::start_slot_worker::<_, _, _, _, _, BabeSlotCompatible, _>(
		config.0,
		select_chain,
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
	threshold: u64,
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
		let ref client = self.client;
		let block_import = self.block_import.clone();
		let ref env = self.env;

		let (timestamp, slot_num, slot_duration) =
			(slot_info.timestamp, slot_info.number, slot_info.duration);

		let authorities = match authorities(client.as_ref(), &BlockId::Hash(chain_head.hash())) {
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

		if !self.force_authoring && self.sync_oracle.is_offline() && authorities.len() > 1 {
			debug!(target: "babe", "Skipping proposal slot. Waiting for the network.");
			telemetry!(CONSENSUS_DEBUG; "babe.skipping_proposal_slot";
				"authorities_len" => authorities.len()
			);
			return Box::new(future::ok(()));
		}

		// FIXME replace the dummy empty slices with real data
		// https://github.com/paritytech/substrate/issues/2435
		// https://github.com/paritytech/substrate/issues/2436
		let authoring_result = if let Some((inout, proof, _batchable_proof)) = claim_slot(
			&[0u8; 0],
			slot_info.number,
			&[0u8; 0],
			0,
			&authorities,
			&pair,
			self.threshold,
		) {
			debug!(
				target: "babe", "Starting authorship at slot {}; timestamp = {}",
				slot_num,
				timestamp,
			);
			telemetry!(CONSENSUS_DEBUG; "babe.starting_authorship";
				"slot_num" => slot_num, "timestamp" => timestamp
			);

			// we are the slot author. make a block and sign it.
			let proposer = match env.init(&chain_head, &authorities) {
				Ok(p) => p,
				Err(e) => {
					warn!(target: "babe", "Unable to author block in slot {:?}: {:?}", slot_num, e);
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
				proposer.propose(
					slot_info.inherent_data,
					remaining_duration,
				).into_future(),
				remaining_duration,
			),
			inout.to_output(),
			proof)
		} else {
			return Box::new(future::ok(()));
		};

		let (proposal_work, vrf_output, proof) = authoring_result;

		Box::new(
			proposal_work
				.map(move |b| {
					// minor hack since we don't have access to the timestamp
					// that is actually set by the proposer.
					let slot_after_building = slot_now(slot_duration);
					if slot_after_building != Some(slot_num) {
						info!(
							target: "babe",
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

					info!(target: "babe",
						  "Pre-sealed block for proposal at {}. Hash now {:?}, previously {:?}.",
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
				.map_err(|e| {
					warn!("Client import failed: {:?}", e);
					consensus_common::ErrorKind::ClientImport(format!("{:?}", e)).into()
				})
		)
	}
}

/// check a header has been signed by the right key. If the slot is too far in
/// the future, an error will be returned. If successful, returns the pre-header
/// and the digest item containing the seal.
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
	threshold: u64,
) -> Result<CheckedHeader<B::Header, DigestItemFor<B>>, String>
	where DigestItemFor<B>: CompatibleDigestItem,
{
	trace!(target: "babe", "Checking header");
	let digest_item = match header.digest_mut().pop() {
		Some(x) => x,
		None => return Err(format!("Header {:?} is unsealed", hash)),
	};

	let BabeSeal {
		slot_num,
		signature: LocalizedSignature {signer, signature },
		proof,
		vrf_output,
	} = digest_item.as_babe_seal().ok_or_else(|| {
		debug!(target: "babe", "Header {:?} is unsealed", hash);
		format!("Header {:?} is unsealed", hash)
	})?;

	if slot_num > slot_now {
		header.digest_mut().push(digest_item);
		Ok(CheckedHeader::Deferred(header, slot_num))
	} else if !authorities.contains(&signer) {
		debug!(target: "babe", "Slot Author not found");
		Err("Slot Author not found".to_string())
	} else {
		let pre_hash = header.hash();
		let to_sign = (slot_num, pre_hash, proof.to_bytes()).encode();

		if sr25519::Pair::verify(&signature, &to_sign[..], &signer) {
			let (inout, _batchable_proof) = {
				let transcript = make_transcript(
					Default::default(),
					slot_num,
					Default::default(),
					0,
				);
				schnorrkel::PublicKey::from_bytes(signer.as_slice()).and_then(|p| {
					p.vrf_verify(transcript, &vrf_output, &proof)
				}).map_err(|s| {
					debug!(target: "babe", "VRF verification failed: {:?}", s);
					format!("VRF verification failed")
				})?
			};
			if check(&inout, threshold) {
				Ok(CheckedHeader::Checked(header, digest_item))
			} else {
				debug!(target: "babe", "VRF verification failed: threshold {} exceeded", threshold);
				Err(format!("Validator {:?} made seal when it wasn’t its turn", signer))
			}
		} else {
			debug!(target: "babe", "Bad signature on {:?}", hash);
			Err(format!("Bad signature on {:?}", hash))
		}
	}
}

/// A verifier for Babe blocks.
pub struct BabeVerifier<C, E> {
	client: Arc<C>,
	extra: E,
	inherent_data_providers: inherents::InherentDataProviders,
	threshold: u64,
}

impl<C, E> BabeVerifier<C, E> {
	fn check_inherents<B: Block>(
		&self,
		block: B,
		block_id: BlockId<B>,
		inherent_data: InherentData,
	) -> Result<(), String>
		where C: ProvideRuntimeApi, C::Api: BlockBuilderApi<B>
	{
		let inherent_res = self.client.runtime_api().check_inherents(
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

/// No-op extra verification.
#[derive(Debug, Clone, Copy)]
pub struct NothingExtra;

impl<B: Block> ExtraVerification<B> for NothingExtra {
	type Verified = Result<(), String>;

	fn verify(&self, _: &B::Header, _: Option<&[B::Extrinsic]>) -> Self::Verified {
		Ok(())
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
		trace!(
			target: "babe",
			"Verifying origin: {:?} header: {:?} justification: {:?} body: {:?}",
			origin,
			header,
			justification,
			body,
		);
		let mut inherent_data = self
			.inherent_data_providers
			.create_inherent_data()
			.map_err(String::from)?;
		let (_, slot_now) = BabeSlotCompatible::extract_timestamp_and_slot(&inherent_data)
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
		// FIXME #1019 in the future, alter this queue to allow deferring of
		// headers
		let checked_header = check_header::<B>(
			slot_now + 1,
			header,
			hash,
			&authorities[..],
			self.threshold,
		)?;
		match checked_header {
			CheckedHeader::Checked(pre_header, seal) => {
				let BabeSeal { slot_num, .. } = seal.as_babe_seal()
					.expect("check_header always returns a seal digest item; qed");

				// if the body is passed through, we need to use the runtime
				// to check that the internally-set timestamp in the inherents
				// actually matches the slot set in the seal.
				if let Some(inner_body) = body.take() {
					inherent_data.babe_replace_inherent_data(slot_num);
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

fn authorities<B, C>(client: &C, at: &BlockId<B>) -> Result<
	Vec<AuthorityIdFor<B>>,
	ConsensusError,
> where
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
				panic!("We don’t support deprecated code with new consensus algorithms, \
						therefore this is unreachable; qed")
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
	debug!(target: "babe", "Registering");
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

fn make_transcript(
	randomness: &[u8],
	slot_number: u64,
	genesis_hash: &[u8],
	epoch: u64,
) -> Transcript {
	let mut transcript = Transcript::new(&BABE_ENGINE_ID);
	transcript.commit_bytes(b"slot number", &slot_number.to_le_bytes());
	transcript.commit_bytes(b"genesis block hash", genesis_hash);
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
	genesis_hash: &[u8],
	epoch: u64,
	authorities: &[sr25519::Public],
	key: &sr25519::Pair,
	threshold: u64,
) -> Option<(VRFInOut, VRFProof, VRFProofBatchable)> {
	if !authorities.contains(&key.public()) { return None }
	let transcript = make_transcript(
		randomness,
		slot_number,
		genesis_hash,
		epoch,
	);

	// Compute the threshold we will use.
	//
	// We already checked that authorities contains `key.public()`, so it can’t
	// be empty.  Therefore, this division is safe.
	let threshold = threshold / authorities.len() as u64;

	get_keypair(key).vrf_sign_n_check(transcript, |inout| check(inout, threshold))
}

#[cfg(test)]
#[allow(dead_code, unused_imports, deprecated)]
// FIXME #2532: need to allow deprecated until refactor is done https://github.com/paritytech/substrate/issues/2532

mod tests {
	use super::*;

	use client::LongestChain;
	use consensus_common::NoNetwork as DummyOracle;
	use network::test::*;
	use network::test::{Block as TestBlock, PeersClient};
	use runtime_primitives::traits::Block as BlockT;
	use network::config::ProtocolConfig;
	use parking_lot::Mutex;
	use tokio::runtime::current_thread;
	use keyring::sr25519::Keyring;
	use client::BlockchainEvents;
	use test_client;
	use futures::stream::Stream;
	use log::debug;
	use std::time::Duration;

	type Error = client::error::Error;

	type TestClient = client::Client<
		test_client::Backend,
		test_client::Executor,
		TestBlock,
		test_client::runtime::RuntimeApi,
	>;

	struct DummyFactory(Arc<TestClient>);
	struct DummyProposer(u64, Arc<TestClient>);

	impl Environment<TestBlock> for DummyFactory {
		type Proposer = DummyProposer;
		type Error = Error;

		fn init(&self, parent_header: &<TestBlock as BlockT>::Header, _authorities: &[Public])
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

	pub struct BabeTestNet {
		peers: Vec<Arc<Peer<(), DummySpecialization>>>,
		started: bool,
	}

	impl TestNetFactory for BabeTestNet {
		type Specialization = DummySpecialization;
		type Verifier = BabeVerifier<PeersClient, NothingExtra>;
		type PeerData = ();

		/// Create new test network with peers and given config.
		fn from_config(_config: &ProtocolConfig) -> Self {
			debug!(target: "babe", "Creating test network from config");
			BabeTestNet {
				peers: Vec::new(),
				started: false,
			}
		}

		fn make_verifier(&self, client: Arc<PeersClient>, _cfg: &ProtocolConfig)
			-> Arc<Self::Verifier>
		{
			trace!(target: "babe", "Creating a verifier");
			let config = Config::get_or_compute(&*client)
				.expect("slot duration available");
			let inherent_data_providers = InherentDataProviders::new();
			register_babe_inherent_data_provider(
				&inherent_data_providers,
				config.get()
			).expect("Registers babe inherent data provider");
			trace!(target: "babe", "Provider registered");

			assert_eq!(config.get(), SLOT_DURATION);
			Arc::new(BabeVerifier {
				client,
				extra: NothingExtra,
				inherent_data_providers,
				threshold: config.threshold(),
			})
		}

		fn peer(&self, i: usize) -> &Peer<Self::PeerData, DummySpecialization> {
			trace!(target: "babe", "Retreiving a peer");
			&self.peers[i]
		}

		fn peers(&self) -> &Vec<Arc<Peer<Self::PeerData, DummySpecialization>>> {
			trace!(target: "babe", "Retreiving peers");
			&self.peers
		}

		fn mut_peers<F: FnOnce(&mut Vec<Arc<Peer<Self::PeerData, DummySpecialization>>>)>(
			&mut self,
			closure: F,
		) {
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
	fn can_serialize_block() {
		drop(env_logger::try_init());
		assert!(BabeSeal::decode(&mut &b""[..]).is_none());
	}

	#[test]
	fn authoring_blocks() {
		drop(env_logger::try_init());
		debug!(target: "babe", "checkpoint 1");
		let mut net = BabeTestNet::new(3);
		debug!(target: "babe", "checkpoint 2");

		net.start();
		debug!(target: "babe", "checkpoint 3");

		let peers = &[
			(0, Keyring::Alice),
			(1, Keyring::Bob),
			(2, Keyring::Charlie),
		];

		let net = Arc::new(Mutex::new(net));
		let mut import_notifications = Vec::new();
		debug!(target: "babe", "checkpoint 4");
		let mut runtime = current_thread::Runtime::new().unwrap();
		for (peer_id, key) in peers {
			let client = net.lock().peer(*peer_id).client().clone();
			let environ = Arc::new(DummyFactory(client.clone()));
			import_notifications.push(
				client.import_notification_stream()
					.take_while(|n| Ok(!(n.origin != BlockOrigin::Own && n.header.number() < &5)))
					.for_each(move |_| Ok(()))
			);

			let config = Config::get_or_compute(&*client)
				.expect("slot duration available");

			let inherent_data_providers = InherentDataProviders::new();
			register_babe_inherent_data_provider(
				&inherent_data_providers, config.get()
			).expect("Registers babe inherent data provider");

			let babe = start_babe(BabeParams {
				config,
				local_key: Arc::new(key.clone().into()),
				block_import: client.clone(),
				select_chain: LongestChain::new(client.backend().clone(), client.import_lock().clone()),
				client,
				env: environ.clone(),
				sync_oracle: DummyOracle,
				on_exit: futures::empty(),
				inherent_data_providers,
				force_authoring: false,
			}).expect("Starts babe");

			runtime.spawn(babe);
		}
		debug!(target: "babe", "checkpoint 5");

		// wait for all finalized on each.
		let wait_for = ::futures::future::join_all(import_notifications)
			.map(drop)
			.map_err(drop);

		let drive_to_completion = ::tokio::timer::Interval::new_interval(TEST_ROUTING_INTERVAL)
			.for_each(move |_| {
				net.lock().send_import_notifications();
				net.lock().sync_without_disconnects();
				Ok(())
			})
			.map(drop)
			.map_err(drop);

		runtime.block_on(wait_for.select(drive_to_completion).map_err(drop)).unwrap();
	}

	#[test]
	#[allow(deprecated)]
	#[should_panic]
	fn old_seals_rejected() {
		drop(env_logger::try_init());
		generic::DigestItem::<network::test::Hash, Public, primitives::sr25519::Signature>::Seal(0, Signature([0; 64])).as_babe_seal().unwrap();
	}

	#[test]
	fn wrong_number_rejected() {
		drop(env_logger::try_init());
		let bad_seal = generic::DigestItem::<network::test::Hash, Public, primitives::sr25519::Signature>::Consensus([0; 4], Signature([0; 64]).encode());
		assert!(bad_seal.as_babe_seal().is_none())
	}

	#[test]
	#[should_panic]
	fn bad_seal_rejected() {
		drop(env_logger::try_init());
		let bad_seal = generic::DigestItem::<network::test::Hash, Public, primitives::sr25519::Signature>::Consensus(BABE_ENGINE_ID, Signature([0; 64]).encode());
		bad_seal.as_babe_seal().expect("we should not decode this successfully");
	}

	#[test]
	fn can_author_block() {
		drop(env_logger::try_init());
		let randomness = &[];
		let pair = sr25519::Pair::generate();
		let mut i = 0;
		loop {
			match claim_slot(randomness, i, &[], 0, &[pair.public()], &pair, u64::MAX / 10) {
				None => i += 1,
				Some(s) => {
					debug!(target: "babe", "Authored block {:?}", s);
					break
				}
			}
		}
	}

	#[test]
	fn authorities_call_works() {
		drop(env_logger::try_init());
		let client = test_client::new();

		assert_eq!(client.info().unwrap().chain.best_number, 0);
		assert_eq!(authorities(&client, &BlockId::Number(0)).unwrap(), vec![
			Keyring::Alice.into(),
			Keyring::Bob.into(),
			Keyring::Charlie.into()
		]);
	}
}
