// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

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
//!
//! NOTE: Aura itself is designed to be generic over the crypto used.
#![forbid(missing_docs, unsafe_code)]
use std::{fmt::Debug, hash::Hash, marker::PhantomData, pin::Pin, sync::Arc};

use futures::prelude::*;

use codec::{Codec, Decode, Encode};

use sc_client_api::{backend::AuxStore, BlockOf};
use sc_consensus::{BlockImport, BlockImportParams, ForkChoiceStrategy, StateAction};
use sc_consensus_slots::{
	BackoffAuthoringBlocksStrategy, InherentDataProviderExt, SimpleSlotWorkerToSlotWorker,
	SlotInfo, StorageChanges,
};
use sc_telemetry::TelemetryHandle;
use sp_api::{Core, ProvideRuntimeApi};
use sp_application_crypto::AppPublic;
use sp_blockchain::HeaderBackend;
use sp_consensus::{BlockOrigin, Environment, Error as ConsensusError, Proposer, SelectChain};
use sp_consensus_slots::Slot;
use sp_core::crypto::{Pair, Public};
use sp_inherents::CreateInherentDataProviders;
use sp_keystore::KeystorePtr;
use sp_runtime::traits::{Block as BlockT, Header, Member, NumberFor};

mod import_queue;
pub mod standalone;

pub use crate::standalone::{find_pre_digest, slot_duration};
pub use import_queue::{
	build_verifier, import_queue, AuraVerifier, BuildVerifierParams, CheckForEquivocation,
	ImportQueueParams,
};
pub use sc_consensus_slots::SlotProportion;
pub use sp_consensus::SyncOracle;
pub use sp_consensus_aura::{
	digests::CompatibleDigestItem,
	inherents::{InherentDataProvider, InherentType as AuraInherent, INHERENT_IDENTIFIER},
	AuraApi, ConsensusLog, SlotDuration, AURA_ENGINE_ID,
};

const LOG_TARGET: &str = "aura";

type AuthorityId<P> = <P as Pair>::Public;

/// Run `AURA` in a compatibility mode.
///
/// This is required for when the chain was launched and later there
/// was a consensus breaking change.
#[derive(Debug, Clone)]
pub enum CompatibilityMode<N> {
	/// Don't use any compatibility mode.
	None,
	/// Call `initialize_block` before doing any runtime calls.
	///
	/// Previously the node would execute `initialize_block` before fetchting the authorities
	/// from the runtime. This behaviour changed in: <https://github.com/paritytech/substrate/pull/9132>
	///
	/// By calling `initialize_block` before fetching the authorities, on a block that
	/// would enact a new validator set, the block would already be build/sealed by an
	/// authority of the new set. With this mode disabled (the default) a block that enacts a new
	/// set isn't sealed/built by an authority of the new set, however to make new nodes be able to
	/// sync old chains this compatibility mode exists.
	UseInitializeBlock {
		/// The block number until this compatibility mode should be executed. The first runtime
		/// call in the context of the `until` block (importing it/building it) will disable the
		/// compatibility mode (i.e. at `until` the default rules will apply). When enabling this
		/// compatibility mode the `until` block should be a future block on which all nodes will
		/// have upgraded to a release that includes the updated compatibility mode configuration.
		/// At `until` block there will be a hard fork when the authority set changes, between the
		/// old nodes (running with `initialize_block`, i.e. without the compatibility mode
		/// configuration) and the new nodes.
		until: N,
	},
}

impl<N> Default for CompatibilityMode<N> {
	fn default() -> Self {
		Self::None
	}
}

/// Parameters of [`start_aura`].
pub struct StartAuraParams<C, SC, I, PF, SO, L, CIDP, BS, N> {
	/// The duration of a slot.
	pub slot_duration: SlotDuration,
	/// The client to interact with the chain.
	pub client: Arc<C>,
	/// A select chain implementation to select the best block.
	pub select_chain: SC,
	/// The block import.
	pub block_import: I,
	/// The proposer factory to build proposer instances.
	pub proposer_factory: PF,
	/// The sync oracle that can give us the current sync status.
	pub sync_oracle: SO,
	/// Hook into the sync module to control the justification sync process.
	pub justification_sync_link: L,
	/// Something that can create the inherent data providers.
	pub create_inherent_data_providers: CIDP,
	/// Should we force the authoring of blocks?
	pub force_authoring: bool,
	/// The backoff strategy when we miss slots.
	pub backoff_authoring_blocks: Option<BS>,
	/// The keystore used by the node.
	pub keystore: KeystorePtr,
	/// The proportion of the slot dedicated to proposing.
	///
	/// The block proposing will be limited to this proportion of the slot from the starting of the
	/// slot. However, the proposing can still take longer when there is some lenience factor
	/// applied, because there were no blocks produced for some slots.
	pub block_proposal_slot_portion: SlotProportion,
	/// The maximum proportion of the slot dedicated to proposing with any lenience factor applied
	/// due to no blocks being produced.
	pub max_block_proposal_slot_portion: Option<SlotProportion>,
	/// Telemetry instance used to report telemetry metrics.
	pub telemetry: Option<TelemetryHandle>,
	/// Compatibility mode that should be used.
	///
	/// If in doubt, use `Default::default()`.
	pub compatibility_mode: CompatibilityMode<N>,
}

/// Start the aura worker. The returned future should be run in a futures executor.
pub fn start_aura<P, B, C, SC, I, PF, SO, L, CIDP, BS, Error>(
	StartAuraParams {
		slot_duration,
		client,
		select_chain,
		block_import,
		proposer_factory,
		sync_oracle,
		justification_sync_link,
		create_inherent_data_providers,
		force_authoring,
		backoff_authoring_blocks,
		keystore,
		block_proposal_slot_portion,
		max_block_proposal_slot_portion,
		telemetry,
		compatibility_mode,
	}: StartAuraParams<C, SC, I, PF, SO, L, CIDP, BS, NumberFor<B>>,
) -> Result<impl Future<Output = ()>, ConsensusError>
where
	P: Pair + Send + Sync,
	P::Public: AppPublic + Hash + Member + Encode + Decode,
	P::Signature: TryFrom<Vec<u8>> + Hash + Member + Encode + Decode,
	B: BlockT,
	C: ProvideRuntimeApi<B> + BlockOf + AuxStore + HeaderBackend<B> + Send + Sync,
	C::Api: AuraApi<B, AuthorityId<P>>,
	SC: SelectChain<B>,
	I: BlockImport<B, Transaction = sp_api::TransactionFor<C, B>> + Send + Sync + 'static,
	PF: Environment<B, Error = Error> + Send + Sync + 'static,
	PF::Proposer: Proposer<B, Error = Error, Transaction = sp_api::TransactionFor<C, B>>,
	SO: SyncOracle + Send + Sync + Clone,
	L: sc_consensus::JustificationSyncLink<B>,
	CIDP: CreateInherentDataProviders<B, ()> + Send + 'static,
	CIDP::InherentDataProviders: InherentDataProviderExt + Send,
	BS: BackoffAuthoringBlocksStrategy<NumberFor<B>> + Send + Sync + 'static,
	Error: std::error::Error + Send + From<ConsensusError> + 'static,
{
	let worker = build_aura_worker::<P, _, _, _, _, _, _, _, _>(BuildAuraWorkerParams {
		client,
		block_import,
		proposer_factory,
		keystore,
		sync_oracle: sync_oracle.clone(),
		justification_sync_link,
		force_authoring,
		backoff_authoring_blocks,
		telemetry,
		block_proposal_slot_portion,
		max_block_proposal_slot_portion,
		compatibility_mode,
	});

	Ok(sc_consensus_slots::start_slot_worker(
		slot_duration,
		select_chain,
		SimpleSlotWorkerToSlotWorker(worker),
		sync_oracle,
		create_inherent_data_providers,
	))
}

/// Parameters of [`build_aura_worker`].
pub struct BuildAuraWorkerParams<C, I, PF, SO, L, BS, N> {
	/// The client to interact with the chain.
	pub client: Arc<C>,
	/// The block import.
	pub block_import: I,
	/// The proposer factory to build proposer instances.
	pub proposer_factory: PF,
	/// The sync oracle that can give us the current sync status.
	pub sync_oracle: SO,
	/// Hook into the sync module to control the justification sync process.
	pub justification_sync_link: L,
	/// Should we force the authoring of blocks?
	pub force_authoring: bool,
	/// The backoff strategy when we miss slots.
	pub backoff_authoring_blocks: Option<BS>,
	/// The keystore used by the node.
	pub keystore: KeystorePtr,
	/// The proportion of the slot dedicated to proposing.
	///
	/// The block proposing will be limited to this proportion of the slot from the starting of the
	/// slot. However, the proposing can still take longer when there is some lenience factor
	/// applied, because there were no blocks produced for some slots.
	pub block_proposal_slot_portion: SlotProportion,
	/// The maximum proportion of the slot dedicated to proposing with any lenience factor applied
	/// due to no blocks being produced.
	pub max_block_proposal_slot_portion: Option<SlotProportion>,
	/// Telemetry instance used to report telemetry metrics.
	pub telemetry: Option<TelemetryHandle>,
	/// Compatibility mode that should be used.
	///
	/// If in doubt, use `Default::default()`.
	pub compatibility_mode: CompatibilityMode<N>,
}

/// Build the aura worker.
///
/// The caller is responsible for running this worker, otherwise it will do nothing.
pub fn build_aura_worker<P, B, C, PF, I, SO, L, BS, Error>(
	BuildAuraWorkerParams {
		client,
		block_import,
		proposer_factory,
		sync_oracle,
		justification_sync_link,
		backoff_authoring_blocks,
		keystore,
		block_proposal_slot_portion,
		max_block_proposal_slot_portion,
		telemetry,
		force_authoring,
		compatibility_mode,
	}: BuildAuraWorkerParams<C, I, PF, SO, L, BS, NumberFor<B>>,
) -> impl sc_consensus_slots::SimpleSlotWorker<
	B,
	Proposer = PF::Proposer,
	BlockImport = I,
	SyncOracle = SO,
	JustificationSyncLink = L,
	Claim = P::Public,
	AuxData = Vec<AuthorityId<P>>,
>
where
	B: BlockT,
	C: ProvideRuntimeApi<B> + BlockOf + AuxStore + HeaderBackend<B> + Send + Sync,
	C::Api: AuraApi<B, AuthorityId<P>>,
	PF: Environment<B, Error = Error> + Send + Sync + 'static,
	PF::Proposer: Proposer<B, Error = Error, Transaction = sp_api::TransactionFor<C, B>>,
	P: Pair + Send + Sync,
	P::Public: AppPublic + Hash + Member + Encode + Decode,
	P::Signature: TryFrom<Vec<u8>> + Hash + Member + Encode + Decode,
	I: BlockImport<B, Transaction = sp_api::TransactionFor<C, B>> + Send + Sync + 'static,
	Error: std::error::Error + Send + From<ConsensusError> + 'static,
	SO: SyncOracle + Send + Sync + Clone,
	L: sc_consensus::JustificationSyncLink<B>,
	BS: BackoffAuthoringBlocksStrategy<NumberFor<B>> + Send + Sync + 'static,
{
	AuraWorker {
		client,
		block_import,
		env: proposer_factory,
		keystore,
		sync_oracle,
		justification_sync_link,
		force_authoring,
		backoff_authoring_blocks,
		telemetry,
		block_proposal_slot_portion,
		max_block_proposal_slot_portion,
		compatibility_mode,
		_key_type: PhantomData::<P>,
	}
}

struct AuraWorker<C, E, I, P, SO, L, BS, N> {
	client: Arc<C>,
	block_import: I,
	env: E,
	keystore: KeystorePtr,
	sync_oracle: SO,
	justification_sync_link: L,
	force_authoring: bool,
	backoff_authoring_blocks: Option<BS>,
	block_proposal_slot_portion: SlotProportion,
	max_block_proposal_slot_portion: Option<SlotProportion>,
	telemetry: Option<TelemetryHandle>,
	compatibility_mode: CompatibilityMode<N>,
	_key_type: PhantomData<P>,
}

#[async_trait::async_trait]
impl<B, C, E, I, P, Error, SO, L, BS> sc_consensus_slots::SimpleSlotWorker<B>
	for AuraWorker<C, E, I, P, SO, L, BS, NumberFor<B>>
where
	B: BlockT,
	C: ProvideRuntimeApi<B> + BlockOf + HeaderBackend<B> + Sync,
	C::Api: AuraApi<B, AuthorityId<P>>,
	E: Environment<B, Error = Error> + Send + Sync,
	E::Proposer: Proposer<B, Error = Error, Transaction = sp_api::TransactionFor<C, B>>,
	I: BlockImport<B, Transaction = sp_api::TransactionFor<C, B>> + Send + Sync + 'static,
	P: Pair + Send + Sync,
	P::Public: AppPublic + Public + Member + Encode + Decode + Hash,
	P::Signature: TryFrom<Vec<u8>> + Member + Encode + Decode + Hash + Debug,
	SO: SyncOracle + Send + Clone + Sync,
	L: sc_consensus::JustificationSyncLink<B>,
	BS: BackoffAuthoringBlocksStrategy<NumberFor<B>> + Send + Sync + 'static,
	Error: std::error::Error + Send + From<ConsensusError> + 'static,
{
	type BlockImport = I;
	type SyncOracle = SO;
	type JustificationSyncLink = L;
	type CreateProposer =
		Pin<Box<dyn Future<Output = Result<E::Proposer, ConsensusError>> + Send + 'static>>;
	type Proposer = E::Proposer;
	type Claim = P::Public;
	type AuxData = Vec<AuthorityId<P>>;

	fn logging_target(&self) -> &'static str {
		"aura"
	}

	fn block_import(&mut self) -> &mut Self::BlockImport {
		&mut self.block_import
	}

	fn aux_data(&self, header: &B::Header, _slot: Slot) -> Result<Self::AuxData, ConsensusError> {
		authorities(
			self.client.as_ref(),
			header.hash(),
			*header.number() + 1u32.into(),
			&self.compatibility_mode,
		)
	}

	fn authorities_len(&self, authorities: &Self::AuxData) -> Option<usize> {
		Some(authorities.len())
	}

	async fn claim_slot(
		&self,
		_header: &B::Header,
		slot: Slot,
		authorities: &Self::AuxData,
	) -> Option<Self::Claim> {
		crate::standalone::claim_slot::<P>(slot, authorities, &self.keystore).await
	}

	fn pre_digest_data(&self, slot: Slot, _claim: &Self::Claim) -> Vec<sp_runtime::DigestItem> {
		vec![crate::standalone::pre_digest::<P>(slot)]
	}

	async fn block_import_params(
		&self,
		header: B::Header,
		header_hash: &B::Hash,
		body: Vec<B::Extrinsic>,
		storage_changes: StorageChanges<<Self::BlockImport as BlockImport<B>>::Transaction, B>,
		public: Self::Claim,
		_authorities: Self::AuxData,
	) -> Result<
		sc_consensus::BlockImportParams<B, <Self::BlockImport as BlockImport<B>>::Transaction>,
		ConsensusError,
	> {
		let signature_digest_item =
			crate::standalone::seal::<_, P>(header_hash, &public, &self.keystore)?;

		let mut import_block = BlockImportParams::new(BlockOrigin::Own, header);
		import_block.post_digests.push(signature_digest_item);
		import_block.body = Some(body);
		import_block.state_action =
			StateAction::ApplyChanges(sc_consensus::StorageChanges::Changes(storage_changes));
		import_block.fork_choice = Some(ForkChoiceStrategy::LongestChain);

		Ok(import_block)
	}

	fn force_authoring(&self) -> bool {
		self.force_authoring
	}

	fn should_backoff(&self, slot: Slot, chain_head: &B::Header) -> bool {
		if let Some(ref strategy) = self.backoff_authoring_blocks {
			if let Ok(chain_head_slot) = find_pre_digest::<B, P::Signature>(chain_head) {
				return strategy.should_backoff(
					*chain_head.number(),
					chain_head_slot,
					self.client.info().finalized_number,
					slot,
					self.logging_target(),
				)
			}
		}
		false
	}

	fn sync_oracle(&mut self) -> &mut Self::SyncOracle {
		&mut self.sync_oracle
	}

	fn justification_sync_link(&mut self) -> &mut Self::JustificationSyncLink {
		&mut self.justification_sync_link
	}

	fn proposer(&mut self, block: &B::Header) -> Self::CreateProposer {
		self.env
			.init(block)
			.map_err(|e| ConsensusError::ClientImport(format!("{:?}", e)))
			.boxed()
	}

	fn telemetry(&self) -> Option<TelemetryHandle> {
		self.telemetry.clone()
	}

	fn proposing_remaining_duration(&self, slot_info: &SlotInfo<B>) -> std::time::Duration {
		let parent_slot = find_pre_digest::<B, P::Signature>(&slot_info.chain_head).ok();

		sc_consensus_slots::proposing_remaining_duration(
			parent_slot,
			slot_info,
			&self.block_proposal_slot_portion,
			self.max_block_proposal_slot_portion.as_ref(),
			sc_consensus_slots::SlotLenienceType::Exponential,
			self.logging_target(),
		)
	}
}

/// Aura Errors
#[derive(Debug, thiserror::Error)]
pub enum Error<B: BlockT> {
	/// Multiple Aura pre-runtime headers
	#[error("Multiple Aura pre-runtime headers")]
	MultipleHeaders,
	/// No Aura pre-runtime digest found
	#[error("No Aura pre-runtime digest found")]
	NoDigestFound,
	/// Header is unsealed
	#[error("Header {0:?} is unsealed")]
	HeaderUnsealed(B::Hash),
	/// Header has a bad seal
	#[error("Header {0:?} has a bad seal")]
	HeaderBadSeal(B::Hash),
	/// Slot Author not found
	#[error("Slot Author not found")]
	SlotAuthorNotFound,
	/// Bad signature
	#[error("Bad signature on {0:?}")]
	BadSignature(B::Hash),
	/// Client Error
	#[error(transparent)]
	Client(sp_blockchain::Error),
	/// Unknown inherent error for identifier
	#[error("Unknown inherent error for identifier: {}", String::from_utf8_lossy(.0))]
	UnknownInherentError(sp_inherents::InherentIdentifier),
	/// Inherents Error
	#[error("Inherent error: {0}")]
	Inherent(sp_inherents::Error),
}

impl<B: BlockT> From<Error<B>> for String {
	fn from(error: Error<B>) -> String {
		error.to_string()
	}
}

impl<B: BlockT> From<crate::standalone::PreDigestLookupError> for Error<B> {
	fn from(e: crate::standalone::PreDigestLookupError) -> Self {
		match e {
			crate::standalone::PreDigestLookupError::MultipleHeaders => Error::MultipleHeaders,
			crate::standalone::PreDigestLookupError::NoDigestFound => Error::NoDigestFound,
		}
	}
}

fn authorities<A, B, C>(
	client: &C,
	parent_hash: B::Hash,
	context_block_number: NumberFor<B>,
	compatibility_mode: &CompatibilityMode<NumberFor<B>>,
) -> Result<Vec<A>, ConsensusError>
where
	A: Codec + Debug,
	B: BlockT,
	C: ProvideRuntimeApi<B>,
	C::Api: AuraApi<B, A>,
{
	let runtime_api = client.runtime_api();

	match compatibility_mode {
		CompatibilityMode::None => {},
		// Use `initialize_block` until we hit the block that should disable the mode.
		CompatibilityMode::UseInitializeBlock { until } =>
			if *until > context_block_number {
				runtime_api
					.initialize_block(
						parent_hash,
						&B::Header::new(
							context_block_number,
							Default::default(),
							Default::default(),
							parent_hash,
							Default::default(),
						),
					)
					.map_err(|_| ConsensusError::InvalidAuthoritiesSet)?;
			},
	}

	runtime_api
		.authorities(parent_hash)
		.ok()
		.ok_or(ConsensusError::InvalidAuthoritiesSet)
}

#[cfg(test)]
mod tests {
	use super::*;
	use parking_lot::Mutex;
	use sc_block_builder::BlockBuilderProvider;
	use sc_client_api::BlockchainEvents;
	use sc_consensus::BoxJustificationImport;
	use sc_consensus_slots::{BackoffAuthoringOnFinalizedHeadLagging, SimpleSlotWorker};
	use sc_keystore::LocalKeystore;
	use sc_network_test::{Block as TestBlock, *};
	use sp_application_crypto::{key_types::AURA, AppCrypto};
	use sp_consensus::{DisableProofRecording, NoNetwork as DummyOracle, Proposal};
	use sp_consensus_aura::sr25519::AuthorityPair;
	use sp_inherents::InherentData;
	use sp_keyring::sr25519::Keyring;
	use sp_keystore::Keystore;
	use sp_runtime::{
		traits::{Block as BlockT, Header as _},
		Digest,
	};
	use sp_timestamp::Timestamp;
	use std::{
		task::Poll,
		time::{Duration, Instant},
	};
	use substrate_test_runtime_client::{
		runtime::{Header, H256},
		TestClient,
	};

	const SLOT_DURATION_MS: u64 = 1000;

	type Error = sp_blockchain::Error;

	struct DummyFactory(Arc<TestClient>);
	struct DummyProposer(u64, Arc<TestClient>);

	impl Environment<TestBlock> for DummyFactory {
		type Proposer = DummyProposer;
		type CreateProposer = futures::future::Ready<Result<DummyProposer, Error>>;
		type Error = Error;

		fn init(&mut self, parent_header: &<TestBlock as BlockT>::Header) -> Self::CreateProposer {
			futures::future::ready(Ok(DummyProposer(parent_header.number + 1, self.0.clone())))
		}
	}

	impl Proposer<TestBlock> for DummyProposer {
		type Error = Error;
		type Transaction =
			sc_client_api::TransactionFor<substrate_test_runtime_client::Backend, TestBlock>;
		type Proposal = future::Ready<Result<Proposal<TestBlock, Self::Transaction, ()>, Error>>;
		type ProofRecording = DisableProofRecording;
		type Proof = ();

		fn propose(
			self,
			_: InherentData,
			digests: Digest,
			_: Duration,
			_: Option<usize>,
		) -> Self::Proposal {
			let r = self.1.new_block(digests).unwrap().build().map_err(|e| e.into());

			future::ready(r.map(|b| Proposal {
				block: b.block,
				proof: (),
				storage_changes: b.storage_changes,
			}))
		}
	}

	type AuraVerifier = import_queue::AuraVerifier<
		PeersFullClient,
		AuthorityPair,
		Box<
			dyn CreateInherentDataProviders<
				TestBlock,
				(),
				InherentDataProviders = (InherentDataProvider,),
			>,
		>,
		u64,
	>;
	type AuraPeer = Peer<(), PeersClient>;

	#[derive(Default)]
	pub struct AuraTestNet {
		peers: Vec<AuraPeer>,
	}

	impl TestNetFactory for AuraTestNet {
		type Verifier = AuraVerifier;
		type PeerData = ();
		type BlockImport = PeersClient;

		fn make_verifier(&self, client: PeersClient, _peer_data: &()) -> Self::Verifier {
			let client = client.as_client();
			let slot_duration = slot_duration(&*client).expect("slot duration available");

			assert_eq!(slot_duration.as_millis() as u64, SLOT_DURATION_MS);
			import_queue::AuraVerifier::new(
				client,
				Box::new(|_, _| async {
					let slot = InherentDataProvider::from_timestamp_and_slot_duration(
						Timestamp::current(),
						SlotDuration::from_millis(SLOT_DURATION_MS),
					);
					Ok((slot,))
				}),
				CheckForEquivocation::Yes,
				None,
				CompatibilityMode::None,
			)
		}

		fn make_block_import(
			&self,
			client: PeersClient,
		) -> (
			BlockImportAdapter<Self::BlockImport>,
			Option<BoxJustificationImport<Block>>,
			Self::PeerData,
		) {
			(client.as_block_import(), None, ())
		}

		fn peer(&mut self, i: usize) -> &mut AuraPeer {
			&mut self.peers[i]
		}

		fn peers(&self) -> &Vec<AuraPeer> {
			&self.peers
		}

		fn peers_mut(&mut self) -> &mut Vec<AuraPeer> {
			&mut self.peers
		}

		fn mut_peers<F: FnOnce(&mut Vec<AuraPeer>)>(&mut self, closure: F) {
			closure(&mut self.peers);
		}
	}

	#[tokio::test]
	async fn authoring_blocks() {
		sp_tracing::try_init_simple();
		let net = AuraTestNet::new(3);

		let peers = &[(0, Keyring::Alice), (1, Keyring::Bob), (2, Keyring::Charlie)];

		let net = Arc::new(Mutex::new(net));
		let mut import_notifications = Vec::new();
		let mut aura_futures = Vec::new();

		let mut keystore_paths = Vec::new();
		for (peer_id, key) in peers {
			let mut net = net.lock();
			let peer = net.peer(*peer_id);
			let client = peer.client().as_client();
			let select_chain = peer.select_chain().expect("full client has a select chain");
			let keystore_path = tempfile::tempdir().expect("Creates keystore path");
			let keystore = Arc::new(
				LocalKeystore::open(keystore_path.path(), None).expect("Creates keystore."),
			);

			keystore
				.sr25519_generate_new(AURA, Some(&key.to_seed()))
				.expect("Creates authority key");
			keystore_paths.push(keystore_path);

			let environ = DummyFactory(client.clone());
			import_notifications.push(
				client
					.import_notification_stream()
					.take_while(|n| {
						future::ready(!(n.origin != BlockOrigin::Own && n.header.number() < &5))
					})
					.for_each(move |_| future::ready(())),
			);

			let slot_duration = slot_duration(&*client).expect("slot duration available");

			aura_futures.push(
				start_aura::<AuthorityPair, _, _, _, _, _, _, _, _, _, _>(StartAuraParams {
					slot_duration,
					block_import: client.clone(),
					select_chain,
					client,
					proposer_factory: environ,
					sync_oracle: DummyOracle,
					justification_sync_link: (),
					create_inherent_data_providers: |_, _| async {
						let slot = InherentDataProvider::from_timestamp_and_slot_duration(
							Timestamp::current(),
							SlotDuration::from_millis(SLOT_DURATION_MS),
						);

						Ok((slot,))
					},
					force_authoring: false,
					backoff_authoring_blocks: Some(
						BackoffAuthoringOnFinalizedHeadLagging::default(),
					),
					keystore,
					block_proposal_slot_portion: SlotProportion::new(0.5),
					max_block_proposal_slot_portion: None,
					telemetry: None,
					compatibility_mode: CompatibilityMode::None,
				})
				.expect("Starts aura"),
			);
		}

		future::select(
			future::poll_fn(move |cx| {
				net.lock().poll(cx);
				Poll::<()>::Pending
			}),
			future::select(future::join_all(aura_futures), future::join_all(import_notifications)),
		)
		.await;
	}

	#[tokio::test]
	async fn current_node_authority_should_claim_slot() {
		let net = AuraTestNet::new(4);

		let mut authorities = vec![
			Keyring::Alice.public().into(),
			Keyring::Bob.public().into(),
			Keyring::Charlie.public().into(),
		];

		let keystore_path = tempfile::tempdir().expect("Creates keystore path");
		let keystore = LocalKeystore::open(keystore_path.path(), None).expect("Creates keystore.");
		let public = keystore
			.sr25519_generate_new(AuthorityPair::ID, None)
			.expect("Key should be created");
		authorities.push(public.into());

		let net = Arc::new(Mutex::new(net));

		let mut net = net.lock();
		let peer = net.peer(3);
		let client = peer.client().as_client();
		let environ = DummyFactory(client.clone());

		let worker = AuraWorker {
			client: client.clone(),
			block_import: client,
			env: environ,
			keystore: keystore.into(),
			sync_oracle: DummyOracle,
			justification_sync_link: (),
			force_authoring: false,
			backoff_authoring_blocks: Some(BackoffAuthoringOnFinalizedHeadLagging::default()),
			telemetry: None,
			_key_type: PhantomData::<AuthorityPair>,
			block_proposal_slot_portion: SlotProportion::new(0.5),
			max_block_proposal_slot_portion: None,
			compatibility_mode: Default::default(),
		};

		let head = Header::new(
			1,
			H256::from_low_u64_be(0),
			H256::from_low_u64_be(0),
			Default::default(),
			Default::default(),
		);
		assert!(worker.claim_slot(&head, 0.into(), &authorities).await.is_none());
		assert!(worker.claim_slot(&head, 1.into(), &authorities).await.is_none());
		assert!(worker.claim_slot(&head, 2.into(), &authorities).await.is_none());
		assert!(worker.claim_slot(&head, 3.into(), &authorities).await.is_some());
		assert!(worker.claim_slot(&head, 4.into(), &authorities).await.is_none());
		assert!(worker.claim_slot(&head, 5.into(), &authorities).await.is_none());
		assert!(worker.claim_slot(&head, 6.into(), &authorities).await.is_none());
		assert!(worker.claim_slot(&head, 7.into(), &authorities).await.is_some());
	}

	#[tokio::test]
	async fn on_slot_returns_correct_block() {
		let net = AuraTestNet::new(4);

		let keystore_path = tempfile::tempdir().expect("Creates keystore path");
		let keystore = LocalKeystore::open(keystore_path.path(), None).expect("Creates keystore.");
		keystore
			.sr25519_generate_new(AuthorityPair::ID, Some(&Keyring::Alice.to_seed()))
			.expect("Key should be created");

		let net = Arc::new(Mutex::new(net));

		let mut net = net.lock();
		let peer = net.peer(3);
		let client = peer.client().as_client();
		let environ = DummyFactory(client.clone());

		let mut worker = AuraWorker {
			client: client.clone(),
			block_import: client.clone(),
			env: environ,
			keystore: keystore.into(),
			sync_oracle: DummyOracle,
			justification_sync_link: (),
			force_authoring: false,
			backoff_authoring_blocks: Option::<()>::None,
			telemetry: None,
			_key_type: PhantomData::<AuthorityPair>,
			block_proposal_slot_portion: SlotProportion::new(0.5),
			max_block_proposal_slot_portion: None,
			compatibility_mode: Default::default(),
		};

		let head = client.expect_header(client.info().genesis_hash).unwrap();

		let res = worker
			.on_slot(SlotInfo {
				slot: 0.into(),
				ends_at: Instant::now() + Duration::from_secs(100),
				create_inherent_data: Box::new(()),
				duration: Duration::from_millis(1000),
				chain_head: head,
				block_size_limit: None,
			})
			.await
			.unwrap();

		// The returned block should be imported and we should be able to get its header by now.
		assert!(client.header(res.block.hash()).unwrap().is_some());
	}
}
