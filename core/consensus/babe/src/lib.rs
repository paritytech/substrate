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
#![forbid(warnings)]
#![forbid(unsafe_code, missing_docs)]
#![allow(unused_imports)]
extern crate core;
pub use babe_primitives::*;
use std::{
	sync::Arc,
	time::Duration,
	thread,
	marker::PhantomData,
	hash::Hash,
	fmt::Debug,
	u64,
};
use parity_codec::{Decode, Encode, Input};
use parking_lot::Mutex;
use runtime_primitives::generic;
use substrate_primitives::{
	crypto::Pair,
	sr25519::{Public, Signature, LocalizedSignature, self},
};
use merlin::Transcript;
use inherents::{InherentDataProviders, InherentData, RuntimeString};
use substrate_telemetry::{telemetry, CONSENSUS_TRACE, CONSENSUS_DEBUG, CONSENSUS_WARN, CONSENSUS_INFO};
use schnorrkel::{
	SecretKey as Secret,
	context::SigningTranscript,
	points::RistrettoBoth,
	keys::Keypair,
	vrf::{VRFProof, VRFProofBatchable, VRF_PROOF_LENGTH, VRFInOut},
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
	runtime_api::{ApiExt, Core as CoreApi},
	error::Result as CResult,
	backend::AuxStore,
};
use runtime_primitives::{generic::BlockId, Justification};
use runtime_primitives::traits::{
	Block, Header, DigestItemFor, DigestItem, ProvideRuntimeApi, AuthorityIdFor,
};

use futures::{Future, IntoFuture, future, stream::Stream};
use tokio::timer::Timeout;
use log::{warn, debug, info};

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
	signature: LocalizedSignature,
	slot_num: u64,
}

impl Encode for BabeSeal {
	fn encode(&self) -> Vec<u8> {
		parity_codec::Encode::encode(&(
			self.proof.to_bytes(),
			self.signature.signature.0,
			self.signature.signer.0,
			self.slot_num,
		))
	}
}

impl Decode for BabeSeal {
	fn decode<R: Input>(i: &mut R) -> Option<Self> {
		let (public_key, proof, sig, slot_num): (
			[u8; PUBLIC_KEY_LENGTH],
			[u8; VRF_PROOF_LENGTH],
			[u8; SIGNATURE_LENGTH],
			u64,
		) = Decode::decode(i)?;
		Some(BabeSeal {
			proof: VRFProof::from_bytes(&proof).ok()?,
			signature: LocalizedSignature {
				signature: Signature(sig),
				signer: Public(public_key),
			},
			slot_num,
		})
	}
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

/// The constant string used to initialize the transcript
pub const TRANSCRIPT_INIT: &'static [u8] = b"substrate-babe";

/// A slot duration. Create with `get_or_compute`.
// FIXME: Once Rust has higher-kinded types, the duplication between this
// and `super::aura::SlotDuration` can be eliminated.
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

struct BabeSlotCompatible;

impl SlotCompatible for BabeSlotCompatible {
	fn extract_timestamp_and_slot(
		data: &InherentData
	) -> Result<(TimestampInherent, u64), consensus_common::Error> {
		data.timestamp_inherent_data()
			.and_then(|t| data.babe_inherent_data().map(|a| (t, a.slot_duration())))
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

struct BabeWorker<C, E, I, SO> {
	client: Arc<C>,
	block_import: Arc<I>,
	env: Arc<E>,
	local_key: Arc<sr25519::Pair>,
	sync_oracle: SO,
	inherent_data_providers: InherentDataProviders,
	force_authoring: bool,
}

fn inherent_to_common_error(err: RuntimeString) -> consensus_common::Error {
	consensus_common::ErrorKind::InherentData(err.into()).into()
}

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

	let mut transcript = Transcript::new(&BABE_ENGINE_ID);
	transcript.proto_name(&BABE_ENGINE_ID);
	transcript.commit_bytes(b"slot number", &slot_number.to_le_bytes());
	transcript.commit_bytes(b"genesis block hash", genesis_hash);
	transcript.commit_bytes(b"current epoch", &epoch.to_le_bytes());
	transcript.commit_bytes(b"chain randomness", randomness);

	let (inout, proof, batchable_proof) = get_keypair(key).vrf_sign(transcript);
	let r: u64 = inout.make_chacharng(b"substrate-babe-vrf").gen();
	if r < threshold {
		Some((inout, proof, batchable_proof))
	} else {
		None
	}
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
		let proposal_work = if let Some(_seal) = author_block(
			&[0u8; 0],
			slot_info.number,
			&[0u8; 0],
			0,
			&authorities, &pair, u64::MAX / 4) {
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
			Timeout::new(
				proposer.propose(slot_info.inherent_data, remaining_duration).into_future(),
				remaining_duration,
			)
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
					let to_sign = (slot_num, pre_hash).encode();
					let signature = pair.sign(&to_sign[..]);
					let item = <DigestItemFor<B> as CompatibleDigestItem>::babe_seal(BabeSeal {
						proof: VRFProof::from_bytes(&[0u8; VRF_PROOF_LENGTH]).expect("FIXME"),
						signature: LocalizedSignature {
							signature,
							signer: pair.public(),
						},
						slot_num,
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