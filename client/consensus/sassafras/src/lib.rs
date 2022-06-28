// This file is part of SubstrateNonepyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! # Sassafras
//!
//! TODO-SASS: documentation

#![forbid(unsafe_code)]
#![warn(missing_docs)]
// TODO-SASS: remove this
#![allow(unused_imports)]

use std::{
	borrow::Cow,
	collections::{BTreeMap, HashMap},
	future::Future,
	pin::Pin,
	sync::Arc,
	task::{Context, Poll},
	time::Duration,
};

use futures::{
	channel::{
		mpsc::{channel, Receiver, Sender},
		oneshot,
	},
	prelude::*,
};
use log::{debug, error, info, log, trace, warn};
use parking_lot::Mutex;
use prometheus_endpoint::Registry;
use retain_mut::RetainMut;
use scale_codec::{Decode, Encode};

use sc_client_api::{
	backend::AuxStore, AuxDataOperations, Backend as BackendT, BlockchainEvents,
	FinalityNotification, PreCommitActions, ProvideUncles, UsageProvider,
};
use sc_consensus::{
	block_import::{
		BlockCheckParams, BlockImport, BlockImportParams, ForkChoiceStrategy, ImportResult,
		StateAction,
	},
	import_queue::{BasicQueue, BoxJustificationImport, DefaultImportQueue, Verifier},
};
use sc_consensus_epochs::{
	descendent_query, Epoch as EpochT, EpochChangesFor, EpochIdentifier, SharedEpochChanges,
	ViableEpochDescriptor,
};
use sc_consensus_slots::{
	check_equivocation, BackoffAuthoringBlocksStrategy, CheckedHeader, InherentDataProviderExt,
	SlotInfo, StorageChanges,
};
use sc_telemetry::{telemetry, TelemetryHandle, CONSENSUS_DEBUG, CONSENSUS_TRACE};
use sp_api::{ApiExt, ProvideRuntimeApi};
use sp_application_crypto::AppKey;
use sp_block_builder::BlockBuilder as BlockBuilderApi;
use sp_blockchain::{
	Backend as _, Error as ClientError, HeaderBackend, HeaderMetadata, Result as ClientResult,
};
use sp_consensus::{
	BlockOrigin, CacheKeyId, CanAuthorWith, Environment, Error as ConsensusError, Proposer,
	SelectChain,
};
use sp_consensus_sassafras::{inherents::SassafrasInherentData, TicketMetadata, VRFProof};
use sp_consensus_slots::{Slot, SlotDuration};
use sp_core::{crypto::ByteArray, traits::SpawnEssentialNamed, ExecutionContext};
use sp_inherents::{CreateInherentDataProviders, InherentData, InherentDataProvider};
use sp_keystore::{SyncCryptoStore, SyncCryptoStorePtr};
use sp_runtime::{
	generic::{BlockId, OpaqueDigestItemId},
	traits::{Block as BlockT, Header, NumberFor, One, SaturatedConversion, Saturating, Zero},
	DigestItem,
};

pub use sp_consensus::SyncOracle;
pub use sp_consensus_sassafras::{
	digests::{
		CompatibleDigestItem, ConsensusLog, NextEpochDescriptor, PreDigest, PrimaryPreDigest,
		SecondaryPreDigest,
	},
	AuthorityId, AuthorityPair, AuthoritySignature, SassafrasApi, SassafrasAuthorityWeight,
	SassafrasEpochConfiguration, SassafrasGenesisConfiguration, Ticket, SASSAFRAS_ENGINE_ID,
	VRF_OUTPUT_LENGTH,
};

mod verification;

pub mod authorship;
pub mod aux_schema;

/// Sassafras epoch information
#[derive(Encode, Decode, PartialEq, Eq, Clone, Debug)]
pub struct Epoch {
	/// The epoch index.
	pub epoch_index: u64,
	/// The starting slot of the epoch.
	pub start_slot: Slot,
	/// The duration of this epoch in slots.
	pub duration: u64,
	/// The authorities and their weights.
	pub authorities: Vec<(AuthorityId, SassafrasAuthorityWeight)>,
	/// Randomness for this epoch.
	pub randomness: [u8; VRF_OUTPUT_LENGTH],
	/// Configuration of the epoch.
	pub config: SassafrasEpochConfiguration,
	/// Tickets metadata.
	pub tickets_info: BTreeMap<Ticket, TicketMetadata>,
}

impl EpochT for Epoch {
	type NextEpochDescriptor = NextEpochDescriptor;
	type Slot = Slot;

	fn increment(&self, descriptor: NextEpochDescriptor) -> Epoch {
		Epoch {
			epoch_index: self.epoch_index + 1,
			start_slot: self.start_slot + self.duration,
			duration: self.duration,
			authorities: descriptor.authorities,
			randomness: descriptor.randomness,
			// TODO-SASS: allow config change on epoch change (i.e. pass as param)
			config: self.config.clone(),
			tickets_info: BTreeMap::new(),
		}
	}

	fn start_slot(&self) -> Slot {
		self.start_slot
	}

	fn end_slot(&self) -> Slot {
		self.start_slot + self.duration
	}
}

impl Epoch {
	/// Create the genesis epoch (epoch #0). This is defined to start at the slot of
	/// the first block, so that has to be provided.
	pub fn genesis(genesis_config: &SassafrasGenesisConfiguration, slot: Slot) -> Epoch {
		Epoch {
			epoch_index: 0,
			start_slot: slot,
			duration: genesis_config.epoch_length,
			authorities: genesis_config.genesis_authorities.clone(),
			randomness: genesis_config.randomness,
			config: SassafrasEpochConfiguration {},
			tickets_info: BTreeMap::new(),
		}
	}
}

/// Errors encountered by the Sassafras authorship task.
/// TODO-SASS: these are BABE errors...
#[derive(Debug, thiserror::Error)]
pub enum Error<B: BlockT> {
	/// Multiple Sassafras pre-runtime digests
	#[error("Multiple Sassafras pre-runtime digests, rejecting!")]
	MultiplePreRuntimeDigests,
	/// No Sassafras pre-runtime digest found
	#[error("No Sassafras pre-runtime digest found")]
	NoPreRuntimeDigest,
	/// Multiple Sassafras epoch change digests
	#[error("Multiple Sassafras epoch change digests, rejecting!")]
	MultipleEpochChangeDigests,
	/// Multiple Sassafras config change digests
	#[error("Multiple Sassafras config change digests, rejecting!")]
	MultipleConfigChangeDigests,
	/// Could not extract timestamp and slot
	#[error("Could not extract timestamp and slot: {0}")]
	Extraction(sp_consensus::Error),
	/// Could not fetch epoch
	#[error("Could not fetch epoch at {0:?}")]
	FetchEpoch(B::Hash),
	/// Header rejected: too far in the future
	#[error("Header {0:?} rejected: too far in the future")]
	TooFarInFuture(B::Hash),
	/// Parent unavailable. Cannot import
	#[error("Parent ({0}) of {1} unavailable. Cannot import")]
	ParentUnavailable(B::Hash, B::Hash),
	/// Slot number must increase
	#[error("Slot number must increase: parent slot: {0}, this slot: {1}")]
	SlotMustIncrease(Slot, Slot),
	/// Header has a bad seal
	#[error("Header {0:?} has a bad seal")]
	HeaderBadSeal(B::Hash),
	/// Header is unsealed
	#[error("Header {0:?} is unsealed")]
	HeaderUnsealed(B::Hash),
	/// Slot author not found
	#[error("Slot author not found")]
	SlotAuthorNotFound,
	/// Secondary slot assignments are disabled for the current epoch.
	#[error("Secondary slot assignments are disabled for the current epoch.")]
	SecondarySlotAssignmentsDisabled,
	/// Bad signature
	#[error("Bad signature on {0:?}")]
	BadSignature(B::Hash),
	/// Invalid author: Expected secondary author
	#[error("Invalid author: Expected secondary author: {0:?}, got: {1:?}.")]
	InvalidAuthor(AuthorityId, AuthorityId),
	/// No secondary author expected.
	#[error("No secondary author expected.")]
	NoSecondaryAuthorExpected,
	/// VRF verification of block by author failed
	#[error("VRF verification of block by author {0:?} failed: threshold {1} exceeded")]
	VRFVerificationOfBlockFailed(AuthorityId, u128),
	// TODO-SASS
	// /// VRF verification failed
	// #[error("VRF verification failed: {0:?}")]
	// VRFVerificationFailed(SignatureError),
	/// Could not fetch parent header
	#[error("Could not fetch parent header: {0}")]
	FetchParentHeader(sp_blockchain::Error),
	/// Expected epoch change to happen.
	#[error("Expected epoch change to happen at {0:?}, s{1}")]
	ExpectedEpochChange(B::Hash, Slot),
	/// Unexpected config change.
	#[error("Unexpected config change")]
	UnexpectedConfigChange,
	/// Unexpected epoch change
	#[error("Unexpected epoch change")]
	UnexpectedEpochChange,
	/// Parent block has no associated weight
	#[error("Parent block of {0} has no associated weight")]
	ParentBlockNoAssociatedWeight(B::Hash),
	/// Check inherents error
	#[error("Checking inherents failed: {0}")]
	CheckInherents(sp_inherents::Error),
	/// Unhandled check inherents error
	#[error("Checking inherents unhandled error: {}", String::from_utf8_lossy(.0))]
	CheckInherentsUnhandled(sp_inherents::InherentIdentifier),
	/// Create inherents error.
	#[error("Creating inherents failed: {0}")]
	CreateInherents(sp_inherents::Error),
	/// Client error
	#[error(transparent)]
	Client(sp_blockchain::Error),
	/// Runtime Api error.
	#[error(transparent)]
	RuntimeApi(sp_api::ApiError),
	/// Fork tree error
	#[error(transparent)]
	ForkTree(Box<fork_tree::Error<sp_blockchain::Error>>),
}

impl<B: BlockT> From<Error<B>> for String {
	fn from(error: Error<B>) -> String {
		error.to_string()
	}
}

fn sassafras_err<B: BlockT>(error: Error<B>) -> Error<B> {
	error!(target: "sassafras", "🌳 {}", error);
	error
}

/// Intermediate value passed to block importer.
pub struct SassafrasIntermediate<B: BlockT> {
	/// The epoch descriptor.
	pub epoch_descriptor: ViableEpochDescriptor<B::Hash, NumberFor<B>, Epoch>,
}

/// Intermediate key for Babe engine.
pub static INTERMEDIATE_KEY: &[u8] = b"sass1";

/// Configuration for Sassafras used for defining block verification parameters as
/// well as authoring (e.g. the slot duration).
#[derive(Clone)]
pub struct Config {
	genesis_config: SassafrasGenesisConfiguration,
}

impl Config {
	/// Read Sassafras genesis configuration from the runtime.
	pub fn get<B: BlockT, C>(client: &C) -> ClientResult<Self>
	where
		C: AuxStore + ProvideRuntimeApi<B> + UsageProvider<B>,
		C::Api: SassafrasApi<B>,
	{
		let mut best_block_id = BlockId::Hash(client.usage_info().chain.best_hash);
		if client.usage_info().chain.finalized_state.is_none() {
			debug!(target: "sassafras", "🌳 No finalized state is available. Reading config from genesis");
			best_block_id = BlockId::Hash(client.usage_info().chain.genesis_hash);
		}

		let genesis_config = client.runtime_api().configuration(&best_block_id)?;

		Ok(Config { genesis_config })
	}

	/// Get the genesis configuration.
	pub fn genesis_config(&self) -> &SassafrasGenesisConfiguration {
		&self.genesis_config
	}

	/// Get the slot duration defined in the genesis configuration.
	pub fn slot_duration(&self) -> SlotDuration {
		SlotDuration::from_millis(self.genesis_config.slot_duration)
	}
}

/// Parameters for Sassafras.
pub struct SassafrasParams<B: BlockT, C, SC, EN, I, SO, L, CIDP, CAW> {
	/// The client to use
	pub client: Arc<C>,

	/// The keystore that manages the keys of the node.
	pub keystore: SyncCryptoStorePtr,

	/// The chain selection strategy
	pub select_chain: SC,

	/// The environment we are producing blocks for.
	pub env: EN,

	/// The underlying block-import object to supply our produced blocks to.
	/// This must be a `SassafrasBlockImport` or a wrapper of it, otherwise
	/// critical consensus logic will be omitted.
	pub block_import: I,

	/// A sync oracle
	pub sync_oracle: SO,

	/// Hook into the sync module to control the justification sync process.
	pub justification_sync_link: L,

	/// Something that can create the inherent data providers.
	pub create_inherent_data_providers: CIDP,

	/// Force authoring of blocks even if we are offline
	pub force_authoring: bool,

	/// The source of timestamps for relative slots
	pub sassafras_link: SassafrasLink<B>,

	/// Checks if the current native implementation can author with a runtime at a given block.
	pub can_author_with: CAW,
	// TODO-SASS
}

/// Start the Sassafras worker.
pub fn start_sassafras<B, C, SC, EN, I, SO, CIDP, CAW, L, ER>(
	SassafrasParams {
		client,
		keystore,
		select_chain,
		env,
		block_import,
		sync_oracle,
		justification_sync_link,
		create_inherent_data_providers,
		force_authoring,
		sassafras_link,
		can_author_with,
	}: SassafrasParams<B, C, SC, EN, I, SO, L, CIDP, CAW>,
) -> Result<SassafrasWorker<B>, sp_consensus::Error>
where
	B: BlockT,
	C: ProvideRuntimeApi<B>
		+ ProvideUncles<B>
		+ BlockchainEvents<B>
		+ PreCommitActions<B>
		+ HeaderBackend<B>
		+ HeaderMetadata<B, Error = ClientError>
		+ Send
		+ Sync
		+ 'static,
	C::Api: SassafrasApi<B>,
	SC: SelectChain<B> + 'static,
	EN: Environment<B, Error = ER> + Send + Sync + 'static,
	EN::Proposer: Proposer<B, Error = ER, Transaction = sp_api::TransactionFor<C, B>>,
	I: BlockImport<B, Error = ConsensusError, Transaction = sp_api::TransactionFor<C, B>>
		+ Send
		+ Sync
		+ 'static,
	SO: SyncOracle + Send + Sync + Clone + 'static,
	L: sc_consensus::JustificationSyncLink<B> + 'static,
	CIDP: CreateInherentDataProviders<B, ()> + Send + Sync + 'static,
	CIDP::InherentDataProviders: InherentDataProviderExt + Send,
	CAW: CanAuthorWith<B> + Send + Sync + 'static,
	ER: std::error::Error + Send + From<ConsensusError> + From<I::Error> + 'static,
{
	const HANDLE_BUFFER_SIZE: usize = 1024;

	info!(target: "sassafras", "🌳 🍁 Starting Sassafras Authorship worker");

	let slot_notification_sinks = Arc::new(Mutex::new(Vec::new()));

	let worker = SassafrasSlotWorker {
		client: client.clone(),
		block_import,
		env,
		sync_oracle: sync_oracle.clone(),
		justification_sync_link,
		force_authoring,
		keystore: keystore.clone(),
		epoch_changes: sassafras_link.epoch_changes.clone(),
		slot_notification_sinks: slot_notification_sinks.clone(),
		config: sassafras_link.config.clone(),
	};

	let slot_worker = sc_consensus_slots::start_slot_worker(
		sassafras_link.config.slot_duration(),
		select_chain.clone(),
		sc_consensus_slots::SimpleSlotWorkerToSlotWorker(worker),
		sync_oracle,
		create_inherent_data_providers,
		can_author_with,
	);

	let ticket_worker = tickets_worker(
		client.clone(),
		keystore,
		sassafras_link.epoch_changes.clone(),
		select_chain,
	);

	// TODO-SASS: proper handler for inbound requests
	let (worker_tx, worker_rx) = channel(HANDLE_BUFFER_SIZE);
	let answer_requests = answer_requests(
		worker_rx,
		sassafras_link.config,
		client.clone(),
		sassafras_link.epoch_changes,
	);

	let inner = async {
		futures::select! {
			_ = slot_worker.fuse() => (),
			_ = ticket_worker.fuse() => (),
			_ = answer_requests.fuse() => (),
		}
	};

	Ok(SassafrasWorker {
		inner: Box::pin(inner.map(|_| ())),
		slot_notification_sinks,
		handle: SassafrasWorkerHandle(worker_tx),
	})
}

async fn tickets_worker<B, C, SC>(
	client: Arc<C>,
	keystore: SyncCryptoStorePtr,
	epoch_changes: SharedEpochChanges<B, Epoch>,
	select_chain: SC,
) where
	B: BlockT,
	C: BlockchainEvents<B> + ProvideRuntimeApi<B>,
	C::Api: SassafrasApi<B>,
	SC: SelectChain<B> + 'static,
{
	use sc_consensus_epochs::EpochIdentifierPosition;

	let mut notifications = client.import_notification_stream();
	while let Some(notification) = notifications.next().await {
		let next_epoch_digest = find_next_epoch_digest::<B>(&notification.header)
			.map_err(|e| ConsensusError::ClientImport(e.to_string()))
			.expect("TODO-SASS: remove me");
		if let Some(epoch_desc) = next_epoch_digest {
			debug!(target: "sassafras", "🌳 New epoch annouced {:x?}", epoch_desc);

			let tickets = {
				let mut epoch_changes = epoch_changes.shared_data();

				let number = *notification.header.number();
				let position = if number == One::one() {
					EpochIdentifierPosition::Genesis1
				} else {
					EpochIdentifierPosition::Regular
				};
				let mut epoch_identifier =
					EpochIdentifier { position, hash: notification.hash, number };

				let epoch = match epoch_changes.epoch_mut(&mut epoch_identifier) {
					Some(epoch) => epoch,
					None => {
						warn!(target: "sassafras", "🌳 Unexpected missing epoch data for {}", notification.hash);
						continue
					},
				};

				authorship::generate_epoch_tickets(epoch, 40, 1, &keystore)
			};

			if tickets.is_empty() {
				continue
			}

			// Get the best block on which we will build and send the tickets.
			let best_id = match select_chain.best_chain().await {
				Ok(header) => BlockId::Hash(header.hash()),
				Err(err) => {
					error!(target: "🌳 sassafras", "{}", err.to_string());
					continue
				},
			};

			if let Err(err) =
				client.runtime_api().submit_tickets_unsigned_extrinsic(&best_id, tickets)
			{
				error!(target: "sassafras", "🌳 Unable to submit tickets: {}", err)
			}

			// TODO-SASS: on error remove tickets from epoch...
		}
	}
}

/// Requests to the Sassafras service.
#[non_exhaustive]
pub enum SassafrasRequest<B: BlockT> {
	/// Request the epoch that a child of the given block, with the given slot number would have.
	///
	/// The parent block is identified by its hash and number.
	EpochForChild(B::Hash, NumberFor<B>, Slot, oneshot::Sender<Result<Epoch, Error<B>>>),
}

async fn answer_requests<B, C>(
	mut request_rx: Receiver<SassafrasRequest<B>>,
	_config: Config,
	_client: Arc<C>,
	_epoch_changes: SharedEpochChanges<B, Epoch>,
) where
	B: BlockT,
	C: ProvideRuntimeApi<B>
		+ ProvideUncles<B>
		+ BlockchainEvents<B>
		+ HeaderBackend<B>
		+ HeaderMetadata<B, Error = ClientError>
		+ Send
		+ Sync
		+ 'static,
{
	while let Some(request) = request_rx.next().await {
		match request {
			SassafrasRequest::EpochForChild(..) => {
				debug!(target: "sassafras", "🌳 Received `EpochForChild` request");
			},
		}
	}
}

/// A handle to the Sassafras worker for issuing requests.
#[derive(Clone)]
pub struct SassafrasWorkerHandle<B: BlockT>(Sender<SassafrasRequest<B>>);

impl<B: BlockT> SassafrasWorkerHandle<B> {
	/// Send a request to the Sassafras service.
	pub async fn send(&mut self, request: SassafrasRequest<B>) {
		// Failure to send means that the service is down.
		// This will manifest as the receiver of the request being dropped.
		let _ = self.0.send(request).await;
	}
}

/// Worker for Sassafras which implements `Future<Output=()>`. This must be polled.
#[must_use]
pub struct SassafrasWorker<B: BlockT> {
	inner: Pin<Box<dyn Future<Output = ()> + Send + 'static>>,
	slot_notification_sinks: SlotNotificationSinks<B>,
	handle: SassafrasWorkerHandle<B>,
}

impl<B: BlockT> Future for SassafrasWorker<B> {
	type Output = ();

	fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		self.inner.as_mut().poll(cx)
	}
}

/// Slot notification sinks.
type SlotNotificationSinks<B> = Arc<
	Mutex<Vec<Sender<(Slot, ViableEpochDescriptor<<B as BlockT>::Hash, NumberFor<B>, Epoch>)>>>,
>;

struct SassafrasSlotWorker<B: BlockT, C, E, I, SO, L> {
	client: Arc<C>,
	block_import: I,
	env: E,
	sync_oracle: SO,
	justification_sync_link: L,
	force_authoring: bool,
	keystore: SyncCryptoStorePtr,
	epoch_changes: SharedEpochChanges<B, Epoch>,
	slot_notification_sinks: SlotNotificationSinks<B>,
	config: Config,
	// TODO-SASS (will be used by authorities_len method)
}

#[async_trait::async_trait]
impl<B, C, E, I, ER, SO, L> sc_consensus_slots::SimpleSlotWorker<B>
	for SassafrasSlotWorker<B, C, E, I, SO, L>
where
	B: BlockT,
	C: ProvideRuntimeApi<B> + HeaderBackend<B> + HeaderMetadata<B, Error = ClientError>,
	C::Api: SassafrasApi<B>,
	E: Environment<B, Error = ER> + Sync,
	E::Proposer: Proposer<B, Error = ER, Transaction = sp_api::TransactionFor<C, B>>,
	I: BlockImport<B, Transaction = sp_api::TransactionFor<C, B>> + Send + Sync + 'static,
	SO: SyncOracle + Send + Clone + Sync,
	L: sc_consensus::JustificationSyncLink<B>,
	ER: std::error::Error + Send + 'static, // TODO-SASS + From<ConsensusError> + From<I::Error>?
{
	type EpochData = ViableEpochDescriptor<B::Hash, NumberFor<B>, Epoch>;
	type Claim = (PreDigest, AuthorityId);
	type SyncOracle = SO;
	type JustificationSyncLink = L;
	type CreateProposer =
		Pin<Box<dyn Future<Output = Result<E::Proposer, sp_consensus::Error>> + Send + 'static>>;
	type Proposer = E::Proposer;
	type BlockImport = I;

	fn logging_target(&self) -> &'static str {
		"sassafras"
	}

	fn block_import(&mut self) -> &mut Self::BlockImport {
		&mut self.block_import
	}

	fn epoch_data(
		&self,
		parent: &B::Header,
		slot: Slot,
	) -> Result<Self::EpochData, ConsensusError> {
		self.epoch_changes
			.shared_data()
			.epoch_descriptor_for_child_of(
				descendent_query(&*self.client),
				&parent.hash(),
				*parent.number(),
				slot,
			)
			.map_err(|e| ConsensusError::ChainLookup(e.to_string()))?
			.ok_or(sp_consensus::Error::InvalidAuthoritiesSet)
	}

	fn authorities_len(&self, epoch_descriptor: &Self::EpochData) -> Option<usize> {
		self.epoch_changes
			.shared_data()
			.viable_epoch(epoch_descriptor, |slot| {
				Epoch::genesis(&self.config.genesis_config, slot)
			})
			.map(|epoch| epoch.as_ref().authorities.len())
	}

	async fn claim_slot(
		&self,
		parent_header: &B::Header,
		slot: Slot,
		epoch_descriptor: &ViableEpochDescriptor<B::Hash, NumberFor<B>, Epoch>,
	) -> Option<Self::Claim> {
		debug!(target: "sassafras", "🌳 Attempting to claim slot {}", slot);

		// Get the next slot ticket
		let block_id = BlockId::Hash(parent_header.hash());

		// TODO-SASS
		// Is this efficient? SHould we instead store the tickets list in the Epoch structure
		// and share it within the `NextEpochData` as done for `randomness`?
		let ticket = self.client.runtime_api().slot_ticket(&block_id, slot).ok()?;

		debug!(target: "sassafras", "🌳 parent {}", parent_header.hash());

		let claim = authorship::claim_slot(
			slot,
			ticket,
			self.epoch_changes
				.shared_data()
				.viable_epoch(epoch_descriptor, |slot| {
					Epoch::genesis(&self.config.genesis_config, slot)
				})?
				.as_ref(),
			&self.keystore,
		);

		if claim.is_some() {
			debug!(target: "sassafras", "🌳 Claimed slot {}", slot);
		}
		claim
	}

	fn notify_slot(
		&self,
		_parent_header: &B::Header,
		slot: Slot,
		epoch_descriptor: &ViableEpochDescriptor<B::Hash, NumberFor<B>, Epoch>,
	) {
		RetainMut::retain_mut(&mut *self.slot_notification_sinks.lock(), |sink| {
			match sink.try_send((slot, epoch_descriptor.clone())) {
				Ok(()) => true,
				Err(e) =>
					if e.is_full() {
						warn!(target: "sassafras", "🌳 Trying to notify a slot but the channel is full");
						true
					} else {
						false
					},
			}
		});
	}

	fn pre_digest_data(&self, _slot: Slot, claim: &Self::Claim) -> Vec<sp_runtime::DigestItem> {
		vec![<DigestItem as CompatibleDigestItem>::sassafras_pre_digest(claim.0.clone())]
	}

	async fn block_import_params(
		&self,
		header: B::Header,
		header_hash: &B::Hash,
		body: Vec<B::Extrinsic>,
		storage_changes: StorageChanges<<Self::BlockImport as BlockImport<B>>::Transaction, B>,
		(_, public): Self::Claim,
		epoch_descriptor: Self::EpochData,
	) -> Result<
		sc_consensus::BlockImportParams<B, <Self::BlockImport as BlockImport<B>>::Transaction>,
		sp_consensus::Error,
	> {
		// Sign the pre-sealed hash of the block and then add it to a digest item.
		let public_type_pair = public.clone().into();
		let public = public.to_raw_vec();
		let signature = SyncCryptoStore::sign_with(
			&*self.keystore,
			<AuthorityId as AppKey>::ID,
			&public_type_pair,
			header_hash.as_ref(),
		)
		.map_err(|e| sp_consensus::Error::CannotSign(public.clone(), e.to_string()))?
		.ok_or_else(|| {
			sp_consensus::Error::CannotSign(
				public.clone(),
				"Could not find key in keystore.".into(),
			)
		})?;
		let signature: AuthoritySignature = signature
			.clone()
			.try_into()
			.map_err(|_| sp_consensus::Error::InvalidSignature(signature, public))?;
		let digest_item = <DigestItem as CompatibleDigestItem>::sassafras_seal(signature);

		let mut import_block = BlockImportParams::new(BlockOrigin::Own, header);
		import_block.post_digests.push(digest_item);
		import_block.body = Some(body);
		import_block.state_action =
			StateAction::ApplyChanges(sc_consensus::StorageChanges::Changes(storage_changes));
		import_block.intermediates.insert(
			Cow::from(INTERMEDIATE_KEY),
			Box::new(SassafrasIntermediate::<B> { epoch_descriptor }) as Box<_>,
		);

		Ok(import_block)
	}

	fn force_authoring(&self) -> bool {
		self.force_authoring
	}

	fn should_backoff(&self, _slot: Slot, _chain_head: &B::Header) -> bool {
		// TODO-SASS
		false
	}

	fn sync_oracle(&mut self) -> &mut Self::SyncOracle {
		&mut self.sync_oracle
	}

	fn justification_sync_link(&mut self) -> &mut Self::JustificationSyncLink {
		&mut self.justification_sync_link
	}

	fn proposer(&mut self, block: &B::Header) -> Self::CreateProposer {
		Box::pin(
			self.env
				.init(block)
				.map_err(|e| sp_consensus::Error::ClientImport(format!("{:?}", e))),
		)
	}

	fn telemetry(&self) -> Option<TelemetryHandle> {
		//TODO-SASS
		None
	}

	fn proposing_remaining_duration(&self, slot_info: &SlotInfo<B>) -> Duration {
		let parent_slot = find_pre_digest::<B>(&slot_info.chain_head).ok().map(|d| d.slot());

		// TODO-SASS : clarify this field. In Sassafras this is part of 'self'
		let block_proposal_slot_portion = sc_consensus_slots::SlotProportion::new(0.5);

		sc_consensus_slots::proposing_remaining_duration(
			parent_slot,
			slot_info,
			&block_proposal_slot_portion,
			None,
			sc_consensus_slots::SlotLenienceType::Exponential,
			self.logging_target(),
		)
	}
}

/// Extract the Sassafras pre digest from the given header. Pre-runtime digests are
/// mandatory, the function will return `Err` if none is found.
pub fn find_pre_digest<B: BlockT>(header: &B::Header) -> Result<PreDigest, Error<B>> {
	// Genesis block doesn't contain a pre digest so let's generate a
	// dummy one to not break any invariants in the rest of the code
	if header.number().is_zero() {
		return Ok(PreDigest::Secondary(SecondaryPreDigest { authority_index: 0, slot: 0.into() }))
	}

	let mut pre_digest: Option<_> = None;
	for log in header.digest().logs() {
		trace!(target: "sassafras", "🌳 Checking log {:?}, looking for pre runtime digest", log);
		match (log.as_sassafras_pre_digest(), pre_digest.is_some()) {
			(Some(_), true) => return Err(sassafras_err(Error::MultiplePreRuntimeDigests)),
			(None, _) => trace!(target: "sassafras", "🌳 Ignoring digest not meant for us"),
			(s, false) => pre_digest = s,
		}
	}
	pre_digest.ok_or_else(|| sassafras_err(Error::NoPreRuntimeDigest))
}

/// Extract the Sassafras epoch change digest from the given header, if it exists.
fn find_next_epoch_digest<B: BlockT>(
	header: &B::Header,
) -> Result<Option<NextEpochDescriptor>, Error<B>> {
	let mut epoch_digest: Option<_> = None;
	for log in header.digest().logs() {
		trace!(target: "sassafras", "🌳 Checking log {:?}, looking for epoch change digest.", log);
		let log = log.try_to::<ConsensusLog>(OpaqueDigestItemId::Consensus(&SASSAFRAS_ENGINE_ID));
		match (log, epoch_digest.is_some()) {
			(Some(ConsensusLog::NextEpochData(_)), true) =>
				return Err(sassafras_err(Error::MultipleEpochChangeDigests)),
			(Some(ConsensusLog::NextEpochData(epoch)), false) => epoch_digest = Some(epoch),
			_ => trace!(target: "sassafras", "🌳 Ignoring digest not meant for us"),
		}
	}

	Ok(epoch_digest)
}

/// State that must be shared between the import queue and the authoring logic.
#[derive(Clone)]
pub struct SassafrasLink<B: BlockT> {
	epoch_changes: SharedEpochChanges<B, Epoch>,
	config: Config,
}

impl<B: BlockT> SassafrasLink<B> {
	/// Get the epoch changes of this link.
	pub fn epoch_changes(&self) -> &SharedEpochChanges<B, Epoch> {
		&self.epoch_changes
	}

	/// Get the config of this link.
	pub fn config(&self) -> &Config {
		&self.config
	}
}

/// A verifier for Sassafras blocks.
pub struct SassafrasVerifier<Block: BlockT, Client, SelectChain, CAW, CIDP> {
	client: Arc<Client>,
	select_chain: SelectChain,
	create_inherent_data_providers: CIDP,
	config: Config,
	epoch_changes: SharedEpochChanges<Block, Epoch>,
	can_author_with: CAW,
	telemetry: Option<TelemetryHandle>,
}

impl<Block, Client, SelectChain, CAW, CIDP> SassafrasVerifier<Block, Client, SelectChain, CAW, CIDP>
where
	Block: BlockT,
	Client: AuxStore + HeaderBackend<Block> + HeaderMetadata<Block> + ProvideRuntimeApi<Block>,
	Client::Api: BlockBuilderApi<Block> + SassafrasApi<Block>,
	SelectChain: sp_consensus::SelectChain<Block>,
	CAW: CanAuthorWith<Block>,
	CIDP: CreateInherentDataProviders<Block, ()>,
{
	async fn check_inherents(
		&self,
		block: Block,
		block_id: BlockId<Block>,
		inherent_data: InherentData,
		create_inherent_data_providers: CIDP::InherentDataProviders,
		execution_context: ExecutionContext,
	) -> Result<(), Error<Block>> {
		if let Err(e) = self.can_author_with.can_author_with(&block_id) {
			debug!(
				target: "sassafras",
				"🌳 Skipping `check_inherents` as authoring version is not compatible: {}",
				e,
			);

			return Ok(())
		}

		let inherent_res = self
			.client
			.runtime_api()
			.check_inherents_with_context(&block_id, execution_context, block, inherent_data)
			.map_err(Error::RuntimeApi)?;

		if !inherent_res.ok() {
			for (i, e) in inherent_res.into_errors() {
				match create_inherent_data_providers.try_handle_error(&i, &e).await {
					Some(res) => res.map_err(|e| Error::CheckInherents(e))?,
					None => return Err(Error::CheckInherentsUnhandled(i)),
				}
			}
		}

		Ok(())
	}

	async fn check_and_report_equivocation(
		&self,
		slot_now: Slot,
		slot: Slot,
		header: &Block::Header,
		author: &AuthorityId,
		origin: &BlockOrigin,
	) -> Result<(), Error<Block>> {
		// Don't report any equivocations during initial sync as they are most likely stale.
		if *origin == BlockOrigin::NetworkInitialSync {
			return Ok(())
		}

		// Check if authorship of this header is an equivocation and return a proof if so.
		let equivocation_proof =
			match check_equivocation(&*self.client, slot_now, slot, header, author)
				.map_err(Error::Client)?
			{
				Some(proof) => proof,
				None => return Ok(()),
			};

		info!(
			"Slot author {:?} is equivocating at slot {} with headers {:?} and {:?}",
			author,
			slot,
			equivocation_proof.first_header.hash(),
			equivocation_proof.second_header.hash(),
		);

		// TODO-SASS

		Ok(())
	}
}

type BlockVerificationResult<Block> =
	Result<(BlockImportParams<Block, ()>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String>;

#[async_trait::async_trait]
impl<Block, Client, SelectChain, CAW, CIDP> Verifier<Block>
	for SassafrasVerifier<Block, Client, SelectChain, CAW, CIDP>
where
	Block: BlockT,
	Client: HeaderMetadata<Block, Error = sp_blockchain::Error>
		+ HeaderBackend<Block>
		+ ProvideRuntimeApi<Block>
		+ Send
		+ Sync
		+ AuxStore,
	Client::Api: BlockBuilderApi<Block> + SassafrasApi<Block>,
	SelectChain: sp_consensus::SelectChain<Block>,
	CAW: CanAuthorWith<Block> + Send + Sync,
	CIDP: CreateInherentDataProviders<Block, ()> + Send + Sync,
	CIDP::InherentDataProviders: InherentDataProviderExt + Send + Sync,
{
	async fn verify(
		&mut self,
		mut block: BlockImportParams<Block, ()>,
	) -> BlockVerificationResult<Block> {
		trace!(
			target: "sassafras",
			"🌳 Verifying origin: {:?} header: {:?} justification(s): {:?} body: {:?}",
			block.origin,
			block.header,
			block.justifications,
			block.body,
		);

		if block.with_state() {
			// When importing whole state we don't calculate epoch descriptor, but rather
			// read it from the state after import. We also skip all verifications
			// because there's no parent state and we trust the sync module to verify
			// that the state is correct and finalized.
			return Ok((block, Default::default()))
		}

		debug!(target: "sassafras", "🌳 We have {:?} logs in this header", block.header.digest().logs().len());

		let hash = block.header.hash();
		let parent_hash = *block.header.parent_hash();

		let create_inherent_data_providers = self
			.create_inherent_data_providers
			.create_inherent_data_providers(parent_hash, ())
			.await
			.map_err(|e| Error::<Block>::Client(sp_consensus::Error::from(e).into()))?;

		let slot_now = create_inherent_data_providers.slot();

		let parent_header_metadata = self
			.client
			.header_metadata(parent_hash)
			.map_err(Error::<Block>::FetchParentHeader)?;

		let pre_digest = find_pre_digest::<Block>(&block.header)?;

		let (check_header, epoch_descriptor) = {
			let epoch_changes = self.epoch_changes.shared_data();
			let epoch_descriptor = epoch_changes
				.epoch_descriptor_for_child_of(
					descendent_query(&*self.client),
					&parent_hash,
					parent_header_metadata.number,
					pre_digest.slot(),
				)
				.map_err(|e| Error::<Block>::ForkTree(Box::new(e)))?
				.ok_or(Error::<Block>::FetchEpoch(parent_hash))?;
			let viable_epoch = epoch_changes
				.viable_epoch(&epoch_descriptor, |slot| {
					Epoch::genesis(&self.config.genesis_config, slot)
				})
				.ok_or(Error::<Block>::FetchEpoch(parent_hash))?;

			// We add one to the current slot to allow for some small drift.
			// FIXME #1019 in the future, alter this queue to allow deferring of headers
			let v_params = verification::VerificationParams {
				header: block.header.clone(),
				pre_digest: Some(pre_digest),
				slot_now: slot_now + 1,
				epoch: viable_epoch.as_ref(),
			};

			(verification::check_header::<Block>(v_params)?, epoch_descriptor)
		};

		// TODO-SASS
		match check_header {
			CheckedHeader::Checked(pre_header, verified_info) => {
				let sassafras_pre_digest = verified_info
					.pre_digest
					.as_sassafras_pre_digest()
					.expect("check_header always returns a pre-digest digest item; qed");
				let slot = sassafras_pre_digest.slot();

				// The header is valid but let's check if there was something else already
				// proposed at the same slot by the given author. If there was, we will
				// report the equivocation to the runtime.
				if let Err(err) = self
					.check_and_report_equivocation(
						slot_now,
						slot,
						&block.header,
						&verified_info.author,
						&block.origin,
					)
					.await
				{
					warn!(target: "sassafras", "🌳 Error checking/reporting Sassafras equivocation: {}", err);
				}

				// If the body is passed through, we need to use the runtime to check that the
				// internally-set timestamp in the inherents actually matches the slot set in the
				// seal.
				if let Some(inner_body) = block.body {
					let mut inherent_data = create_inherent_data_providers
						.create_inherent_data()
						.map_err(Error::<Block>::CreateInherents)?;
					inherent_data.sassafras_replace_inherent_data(slot);
					let new_block = Block::new(pre_header.clone(), inner_body);

					self.check_inherents(
						new_block.clone(),
						BlockId::Hash(parent_hash),
						inherent_data,
						create_inherent_data_providers,
						block.origin.into(),
					)
					.await?;

					let (_, inner_body) = new_block.deconstruct();
					block.body = Some(inner_body);
				}

				trace!(target: "sassafras", "🌳 Checked {:?}; importing.", pre_header);
				telemetry!(
					self.telemetry;
					CONSENSUS_TRACE;
					"sassafras.checked_and_importing";
					"pre_header" => ?pre_header,
				);

				block.header = pre_header;
				block.post_digests.push(verified_info.seal);
				block.intermediates.insert(
					Cow::from(INTERMEDIATE_KEY),
					Box::new(SassafrasIntermediate::<Block> { epoch_descriptor }) as Box<_>,
				);
				block.post_hash = Some(hash);

				Ok((block, Default::default()))
			},
			CheckedHeader::Deferred(a, b) => {
				debug!(target: "sassafras", "🌳 Checking {:?} failed; {:?}, {:?}.", hash, a, b);
				telemetry!(
					self.telemetry;
					CONSENSUS_DEBUG;
					"sassafras.header_too_far_in_future";
					"hash" => ?hash, "a" => ?a, "b" => ?b
				);
				Err(Error::<Block>::TooFarInFuture(hash).into())
			},
		}
	}
}

/// A block-import handler for Sassafras.
///
/// This scans each imported block for epoch change announcements. The announcements are
/// tracked in a tree (of all forks), and the import logic validates all epoch change
/// transitions, i.e. whether a given epoch change is expected or whether it is missing.
///
/// The epoch change tree should be pruned as blocks are finalized.
pub struct SassafrasBlockImport<B: BlockT, C, I> {
	inner: I,
	client: Arc<C>,
	epoch_changes: SharedEpochChanges<B, Epoch>,
	config: Config,
}

impl<Block: BlockT, I: Clone, Client> Clone for SassafrasBlockImport<Block, Client, I> {
	fn clone(&self) -> Self {
		SassafrasBlockImport {
			inner: self.inner.clone(),
			client: self.client.clone(),
			epoch_changes: self.epoch_changes.clone(),
			config: self.config.clone(),
		}
	}
}

impl<B: BlockT, C, I> SassafrasBlockImport<B, C, I> {
	fn new(
		client: Arc<C>,
		epoch_changes: SharedEpochChanges<B, Epoch>,
		block_import: I,
		config: Config,
	) -> Self {
		SassafrasBlockImport { client, inner: block_import, epoch_changes, config }
	}
}

#[async_trait::async_trait]
impl<Block, Client, Inner> BlockImport<Block> for SassafrasBlockImport<Block, Client, Inner>
where
	Block: BlockT,
	Inner: BlockImport<Block, Transaction = sp_api::TransactionFor<Client, Block>> + Send + Sync,
	Inner::Error: Into<ConsensusError>,
	Client: HeaderBackend<Block>
		+ HeaderMetadata<Block, Error = sp_blockchain::Error>
		+ AuxStore
		+ ProvideRuntimeApi<Block>
		+ Send
		+ Sync,
	Client::Api: SassafrasApi<Block> + ApiExt<Block>,
{
	type Error = ConsensusError;
	type Transaction = sp_api::TransactionFor<Client, Block>;

	async fn import_block(
		&mut self,
		mut block: BlockImportParams<Block, Self::Transaction>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		let hash = block.post_hash();
		let number = *block.header.number();

		let pre_digest = find_pre_digest::<Block>(&block.header).expect(
			"valid sassafras headers must contain a predigest; header has been already verified; qed",
		);
		let slot = pre_digest.slot();

		let parent_hash = *block.header.parent_hash();
		let parent_header = self
			.client
			.header(BlockId::Hash(parent_hash))
			.map_err(|e| ConsensusError::ChainLookup(e.to_string()))?
			.ok_or_else(|| {
				ConsensusError::ChainLookup(
					sassafras_err(Error::<Block>::ParentUnavailable(parent_hash, hash)).into(),
				)
			})?;

		let parent_slot = find_pre_digest::<Block>(&parent_header).map(|d| d.slot()).expect(
			"parent is non-genesis; valid Sassafras headers contain a pre-digest; \
             header has already been verified; qed",
		);

		// Make sure that slot number is strictly increasing
		if slot <= parent_slot {
			return Err(ConsensusError::ClientImport(
				sassafras_err(Error::<Block>::SlotMustIncrease(parent_slot, slot)).into(),
			))
		}

		// If there's a pending epoch we'll save the previous epoch changes here
		// this way we can revert it if there's any error
		let mut old_epoch_changes = None;

		// Use an extra scope to make the compiler happy, because otherwise he complains about the
		// mutex, even if we dropped it...
		let mut epoch_changes = {
			let mut epoch_changes = self.epoch_changes.shared_data_locked();

			// Check if there's any epoch change expected to happen at this slot.
			// `epoch` is the epoch to verify the block under, and `first_in_epoch` is true
			// if this is the first block in its chain for that epoch.
			//
			// also provides the total weight of the chain, including the imported block.
			let parent_weight = if *parent_header.number() == Zero::zero() {
				0
			} else {
				aux_schema::load_block_weight(&*self.client, parent_hash)
					.map_err(|e| ConsensusError::ClientImport(e.to_string()))?
					.ok_or_else(|| {
						ConsensusError::ClientImport(
							sassafras_err(Error::<Block>::ParentBlockNoAssociatedWeight(hash))
								.into(),
						)
					})?
			};

			let intermediate =
				block.take_intermediate::<SassafrasIntermediate<Block>>(INTERMEDIATE_KEY)?;

			let epoch_descriptor = intermediate.epoch_descriptor;
			let first_in_epoch = parent_slot < epoch_descriptor.start_slot();

			let total_weight = parent_weight + pre_digest.added_weight();

			// Search for this all the time so we can reject unexpected announcements.
			let next_epoch_digest = find_next_epoch_digest::<Block>(&block.header)
				.map_err(|e| ConsensusError::ClientImport(e.to_string()))?;

			match (first_in_epoch, next_epoch_digest.is_some()) {
				(true, false) =>
					return Err(ConsensusError::ClientImport(
						sassafras_err(Error::<Block>::ExpectedEpochChange(hash, slot)).into(),
					)),
				(false, true) =>
					return Err(ConsensusError::ClientImport(
						sassafras_err(Error::<Block>::UnexpectedEpochChange).into(),
					)),
				_ => (),
			}

			let info = self.client.info();

			if let Some(next_epoch_descriptor) = next_epoch_digest {
				old_epoch_changes = Some((*epoch_changes).clone());

				let viable_epoch = epoch_changes
					.viable_epoch(&epoch_descriptor, |slot| {
						Epoch::genesis(&self.config.genesis_config, slot)
					})
					.ok_or_else(|| {
						ConsensusError::ClientImport(Error::<Block>::FetchEpoch(parent_hash).into())
					})?;

				// restrict info logging during initial sync to avoid spam
				let log_level = if block.origin == BlockOrigin::NetworkInitialSync {
					log::Level::Debug
				} else {
					log::Level::Info
				};

				log!(target: "sassafras",
					 log_level,
					 "🌳 🍁 New epoch {} launching at block {} (block slot {} >= start slot {}).",
					 viable_epoch.as_ref().epoch_index,
					 hash,
					 slot,
					 viable_epoch.as_ref().start_slot,
				);

				let next_epoch = viable_epoch.increment(next_epoch_descriptor);

				log!(target: "sassafras",
					 log_level,
					 "🌳 🍁 Next epoch starts at slot {}",
					 next_epoch.as_ref().start_slot,
				);

				// Prune the tree of epochs not part of the finalized chain or
				// that are not live anymore, and then track the given epoch change
				// in the tree.
				// NOTE: it is important that these operations are done in this
				// order, otherwise if pruning after import the `is_descendent_of`
				// used by pruning may not know about the block that is being
				// imported.
				let prune_and_import = || {
					prune_finalized(self.client.clone(), &mut epoch_changes)?;

					epoch_changes
						.import(
							descendent_query(&*self.client),
							hash,
							number,
							*block.header.parent_hash(),
							next_epoch,
						)
						.map_err(|e| {
							ConsensusError::ClientImport(format!(
								"Error importing epoch changes: {}",
								e
							))
						})?;

					Ok(())
				};

				if let Err(e) = prune_and_import() {
					debug!(target: "sassafras", "🌳 Failed to launch next epoch: {}", e);
					*epoch_changes =
						old_epoch_changes.expect("set `Some` above and not taken; qed");
					return Err(e)
				}

				aux_schema::write_epoch_changes::<Block, _, _>(&*epoch_changes, |insert| {
					block
						.auxiliary
						.extend(insert.iter().map(|(k, v)| (k.to_vec(), Some(v.to_vec()))))
				});
			}

			aux_schema::write_block_weight(hash, total_weight, |values| {
				block
					.auxiliary
					.extend(values.iter().map(|(k, v)| (k.to_vec(), Some(v.to_vec()))))
			});

			// The fork choice rule is that we pick the heaviest chain (i.e.
			// more primary blocks), if there's a tie we go with the longest
			// chain.
			block.fork_choice = {
				let (last_best, last_best_number) = (info.best_hash, info.best_number);

				let last_best_weight = if &last_best == block.header.parent_hash() {
					// the parent=genesis case is already covered for loading parent weight,
					// so we don't need to cover again here.
					parent_weight
				} else {
					aux_schema::load_block_weight(&*self.client, last_best)
						.map_err(|e| ConsensusError::ChainLookup(e.to_string()))?
						.ok_or_else(|| {
							ConsensusError::ChainLookup(
								"No block weight for parent header.".to_string(),
							)
						})?
				};

				Some(ForkChoiceStrategy::Custom(if total_weight > last_best_weight {
					true
				} else if total_weight == last_best_weight {
					number > last_best_number
				} else {
					false
				}))
			};
			// Release the mutex, but it stays locked
			epoch_changes.release_mutex()
		};

		let import_result = self.inner.import_block(block, new_cache).await;

		// Revert to the original epoch changes in case there's an error
		// importing the block
		if import_result.is_err() {
			if let Some(old_epoch_changes) = old_epoch_changes {
				*epoch_changes.upgrade() = old_epoch_changes;
			}
		}

		import_result.map_err(Into::into)
	}

	async fn check_block(
		&mut self,
		block: BlockCheckParams<Block>,
	) -> Result<ImportResult, Self::Error> {
		self.inner.check_block(block).await.map_err(Into::into)
	}
}

/// Gets the best finalized block and its slot, and prunes the given epoch tree.
fn prune_finalized<C, B>(
	client: Arc<C>,
	epoch_changes: &mut EpochChangesFor<B, Epoch>,
) -> Result<(), ConsensusError>
where
	B: BlockT,
	C: HeaderBackend<B> + HeaderMetadata<B, Error = sp_blockchain::Error>,
{
	let info = client.info();
	if info.block_gap.is_none() {
		epoch_changes.clear_gap();
	}

	let finalized_slot = {
		let finalized_header = client
			.header(BlockId::Hash(info.finalized_hash))
			.map_err(|e| ConsensusError::ClientImport(e.to_string()))?
			.expect(
				"best finalized hash was given by client; finalized headers must exist in db; qed",
			);

		find_pre_digest::<B>(&finalized_header)
			.expect("finalized header must be valid; valid blocks have a pre-digest; qed")
			.slot()
	};

	epoch_changes
		.prune_finalized(
			descendent_query(&*client),
			&info.finalized_hash,
			info.finalized_number,
			finalized_slot,
		)
		.map_err(|e| ConsensusError::ClientImport(e.to_string()))?;

	Ok(())
}

/// Produce a Sassafras block-import object to be used later on in the construction of
/// an import-queue.
///
/// Also returns a link object used to correctly instantiate the import queue
/// and background worker.
pub fn block_import<C, B: BlockT, I>(
	config: Config,
	wrapped_block_import: I,
	client: Arc<C>,
) -> ClientResult<(SassafrasBlockImport<B, C, I>, SassafrasLink<B>)>
where
	C: AuxStore + HeaderBackend<B> + HeaderMetadata<B, Error = sp_blockchain::Error> + 'static,
{
	let epoch_changes = aux_schema::load_epoch_changes::<B, _>(&*client)?;

	let link = SassafrasLink { epoch_changes: epoch_changes.clone(), config: config.clone() };

	// NOTE: this isn't entirely necessary, but since we didn't use to prune the
	// epoch tree it is useful as a migration, so that nodes prune long trees on
	// startup rather than waiting until importing the next epoch change block.
	prune_finalized(client.clone(), &mut epoch_changes.shared_data())?;

	// TODO-SASS: If required, register on-finality actions (e.g. aux data cleanup)

	let import = SassafrasBlockImport::new(client, epoch_changes, wrapped_block_import, config);

	Ok((import, link))
}

/// Start an import queue for the Sassafras consensus algorithm.
///
/// This method returns the import queue, some data that needs to be passed to the block authoring
/// logic (`SassafrasLink`), and a future that must be run to completion and is responsible for
/// listening to finality notifications and pruning the epoch changes tree.
///
/// The block import object provided must be the `SassafrasBlockImport` or a wrapper of it,
/// otherwise crucial import logic will be omitted.
pub fn import_queue<Block: BlockT, Client, SelectChain, Inner, CAW, CIDP>(
	sassafras_link: SassafrasLink<Block>,
	block_import: Inner,
	justification_import: Option<BoxJustificationImport<Block>>,
	client: Arc<Client>,
	select_chain: SelectChain,
	create_inherent_data_providers: CIDP,
	spawner: &impl sp_core::traits::SpawnEssentialNamed,
	registry: Option<&Registry>,
	can_author_with: CAW,
	telemetry: Option<TelemetryHandle>,
) -> ClientResult<DefaultImportQueue<Block, Client>>
where
	Inner: BlockImport<
			Block,
			Error = ConsensusError,
			Transaction = sp_api::TransactionFor<Client, Block>,
		> + Send
		+ Sync
		+ 'static,
	Client: ProvideRuntimeApi<Block>
		+ HeaderBackend<Block>
		+ HeaderMetadata<Block, Error = sp_blockchain::Error>
		+ AuxStore
		+ Send
		+ Sync
		+ 'static,
	Client::Api: BlockBuilderApi<Block> + SassafrasApi<Block> + ApiExt<Block>,
	SelectChain: sp_consensus::SelectChain<Block> + 'static,
	CAW: CanAuthorWith<Block> + Send + Sync + 'static,
	CIDP: CreateInherentDataProviders<Block, ()> + Send + Sync + 'static,
	CIDP::InherentDataProviders: InherentDataProviderExt + Send + Sync,
{
	let verifier = SassafrasVerifier {
		select_chain,
		create_inherent_data_providers,
		config: sassafras_link.config,
		epoch_changes: sassafras_link.epoch_changes,
		can_author_with,
		telemetry,
		client,
	};

	Ok(BasicQueue::new(verifier, Box::new(block_import), justification_import, spawner, registry))
}
