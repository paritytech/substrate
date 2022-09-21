// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! # BABE (Blind Assignment for Blockchain Extension)
//!
//! BABE is a slot-based block production mechanism which uses a VRF PRNG to
//! randomly perform the slot allocation. On every slot, all the authorities
//! generate a new random number with the VRF function and if it is lower than a
//! given threshold (which is proportional to their weight/stake) they have a
//! right to produce a block. The proof of the VRF function execution will be
//! used by other peer to validate the legitimacy of the slot claim.
//!
//! The engine is also responsible for collecting entropy on-chain which will be
//! used to seed the given VRF PRNG. An epoch is a contiguous number of slots
//! under which we will be using the same authority set. During an epoch all VRF
//! outputs produced as a result of block production will be collected on an
//! on-chain randomness pool. Epoch changes are announced one epoch in advance,
//! i.e. when ending epoch N, we announce the parameters (randomness,
//! authorities, etc.) for epoch N+2.
//!
//! Since the slot assignment is randomized, it is possible that a slot is
//! assigned to multiple validators in which case we will have a temporary fork,
//! or that a slot is assigned to no validator in which case no block is
//! produced. Which means that block times are not deterministic.
//!
//! The protocol has a parameter `c` [0, 1] for which `1 - c` is the probability
//! of a slot being empty. The choice of this parameter affects the security of
//! the protocol relating to maximum tolerable network delays.
//!
//! In addition to the VRF-based slot assignment described above, which we will
//! call primary slots, the engine also supports a deterministic secondary slot
//! assignment. Primary slots take precedence over secondary slots, when
//! authoring the node starts by trying to claim a primary slot and falls back
//! to a secondary slot claim attempt. The secondary slot assignment is done
//! by picking the authority at index:
//!
//! `blake2_256(epoch_randomness ++ slot_number) % authorities_len`.
//!
//! The secondary slots supports either a `SecondaryPlain` or `SecondaryVRF`
//! variant. Comparing with `SecondaryPlain` variant, the `SecondaryVRF` variant
//! generates an additional VRF output. The output is not included in beacon
//! randomness, but can be consumed by parachains.
//!
//! The fork choice rule is weight-based, where weight equals the number of
//! primary blocks in the chain. We will pick the heaviest chain (more primary
//! blocks) and will go with the longest one in case of a tie.
//!
//! An in-depth description and analysis of the protocol can be found here:
//! <https://research.web3.foundation/en/latest/polkadot/block-production/Babe.html>

#![forbid(unsafe_code)]
#![warn(missing_docs)]

use std::{
	collections::{HashMap, HashSet},
	future::Future,
	pin::Pin,
	sync::Arc,
	task::{Context, Poll},
	time::Duration,
};

use codec::{Decode, Encode};
use futures::{
	channel::{
		mpsc::{channel, Receiver, Sender},
		oneshot,
	},
	prelude::*,
};
use log::{debug, info, log, trace, warn};
use parking_lot::Mutex;
use prometheus_endpoint::Registry;
use schnorrkel::SignatureError;

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
	descendent_query, Epoch as EpochT, EpochChangesFor, SharedEpochChanges, ViableEpochDescriptor,
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
	BlockOrigin, CacheKeyId, Environment, Error as ConsensusError, Proposer, SelectChain,
};
use sp_consensus_babe::inherents::BabeInherentData;
use sp_consensus_slots::Slot;
use sp_core::{crypto::ByteArray, ExecutionContext};
use sp_inherents::{CreateInherentDataProviders, InherentData, InherentDataProvider};
use sp_keystore::{SyncCryptoStore, SyncCryptoStorePtr};
use sp_runtime::{
	generic::{BlockId, OpaqueDigestItemId},
	traits::{Block as BlockT, Header, NumberFor, SaturatedConversion, Saturating, Zero},
	DigestItem,
};

pub use sc_consensus_slots::SlotProportion;
pub use sp_consensus::SyncOracle;
pub use sp_consensus_babe::{
	digests::{
		CompatibleDigestItem, NextConfigDescriptor, NextEpochDescriptor, PreDigest,
		PrimaryPreDigest, SecondaryPlainPreDigest,
	},
	AuthorityId, AuthorityPair, AuthoritySignature, BabeApi, BabeAuthorityWeight, BabeBlockWeight,
	BabeConfiguration, BabeEpochConfiguration, ConsensusLog, BABE_ENGINE_ID, VRF_OUTPUT_LENGTH,
};

pub use aux_schema::load_block_weight as block_weight;

mod migration;
mod verification;

pub mod authorship;
pub mod aux_schema;
#[cfg(test)]
mod tests;

/// BABE epoch information
#[derive(Decode, Encode, PartialEq, Eq, Clone, Debug)]
pub struct Epoch {
	/// The epoch index.
	pub epoch_index: u64,
	/// The starting slot of the epoch.
	pub start_slot: Slot,
	/// The duration of this epoch.
	pub duration: u64,
	/// The authorities and their weights.
	pub authorities: Vec<(AuthorityId, BabeAuthorityWeight)>,
	/// Randomness for this epoch.
	pub randomness: [u8; VRF_OUTPUT_LENGTH],
	/// Configuration of the epoch.
	pub config: BabeEpochConfiguration,
}

impl EpochT for Epoch {
	type NextEpochDescriptor = (NextEpochDescriptor, BabeEpochConfiguration);
	type Slot = Slot;

	fn increment(
		&self,
		(descriptor, config): (NextEpochDescriptor, BabeEpochConfiguration),
	) -> Epoch {
		Epoch {
			epoch_index: self.epoch_index + 1,
			start_slot: self.start_slot + self.duration,
			duration: self.duration,
			authorities: descriptor.authorities,
			randomness: descriptor.randomness,
			config,
		}
	}

	fn start_slot(&self) -> Slot {
		self.start_slot
	}

	fn end_slot(&self) -> Slot {
		self.start_slot + self.duration
	}
}

impl From<sp_consensus_babe::Epoch> for Epoch {
	fn from(epoch: sp_consensus_babe::Epoch) -> Self {
		Epoch {
			epoch_index: epoch.epoch_index,
			start_slot: epoch.start_slot,
			duration: epoch.duration,
			authorities: epoch.authorities,
			randomness: epoch.randomness,
			config: epoch.config,
		}
	}
}

impl Epoch {
	/// Create the genesis epoch (epoch #0). This is defined to start at the slot of
	/// the first block, so that has to be provided.
	pub fn genesis(genesis_config: &BabeConfiguration, slot: Slot) -> Epoch {
		Epoch {
			epoch_index: 0,
			start_slot: slot,
			duration: genesis_config.epoch_length,
			authorities: genesis_config.authorities.clone(),
			randomness: genesis_config.randomness,
			config: BabeEpochConfiguration {
				c: genesis_config.c,
				allowed_slots: genesis_config.allowed_slots,
			},
		}
	}
}

/// Errors encountered by the babe authorship task.
#[derive(Debug, thiserror::Error)]
pub enum Error<B: BlockT> {
	/// Multiple BABE pre-runtime digests
	#[error("Multiple BABE pre-runtime digests, rejecting!")]
	MultiplePreRuntimeDigests,
	/// No BABE pre-runtime digest found
	#[error("No BABE pre-runtime digest found")]
	NoPreRuntimeDigest,
	/// Multiple BABE epoch change digests
	#[error("Multiple BABE epoch change digests, rejecting!")]
	MultipleEpochChangeDigests,
	/// Multiple BABE config change digests
	#[error("Multiple BABE config change digests, rejecting!")]
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
	/// VRF verification failed
	#[error("VRF verification failed: {0:?}")]
	VRFVerificationFailed(SignatureError),
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

fn babe_err<B: BlockT>(error: Error<B>) -> Error<B> {
	debug!(target: "babe", "{}", error);
	error
}

/// Intermediate value passed to block importer.
pub struct BabeIntermediate<B: BlockT> {
	/// The epoch descriptor.
	pub epoch_descriptor: ViableEpochDescriptor<B::Hash, NumberFor<B>, Epoch>,
}

/// Intermediate key for Babe engine.
pub static INTERMEDIATE_KEY: &[u8] = b"babe1";

/// Read configuration from the runtime state at current best block.
pub fn configuration<B: BlockT, C>(client: &C) -> ClientResult<BabeConfiguration>
where
	C: AuxStore + ProvideRuntimeApi<B> + UsageProvider<B>,
	C::Api: BabeApi<B>,
{
	let block_id = if client.usage_info().chain.finalized_state.is_some() {
		BlockId::Hash(client.usage_info().chain.best_hash)
	} else {
		debug!(target: "babe", "No finalized state is available. Reading config from genesis");
		BlockId::Hash(client.usage_info().chain.genesis_hash)
	};

	let runtime_api = client.runtime_api();
	let version = runtime_api.api_version::<dyn BabeApi<B>>(&block_id)?;

	let config = match version {
		Some(1) => {
			#[allow(deprecated)]
			{
				runtime_api.configuration_before_version_2(&block_id)?.into()
			}
		},
		Some(2) => runtime_api.configuration(&block_id)?,
		_ =>
			return Err(sp_blockchain::Error::VersionInvalid(
				"Unsupported or invalid BabeApi version".to_string(),
			)),
	};
	Ok(config)
}

/// Parameters for BABE.
pub struct BabeParams<B: BlockT, C, SC, E, I, SO, L, CIDP, BS> {
	/// The keystore that manages the keys of the node.
	pub keystore: SyncCryptoStorePtr,

	/// The client to use
	pub client: Arc<C>,

	/// The SelectChain Strategy
	pub select_chain: SC,

	/// The environment we are producing blocks for.
	pub env: E,

	/// The underlying block-import object to supply our produced blocks to.
	/// This must be a `BabeBlockImport` or a wrapper of it, otherwise
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

	/// Strategy and parameters for backing off block production.
	pub backoff_authoring_blocks: Option<BS>,

	/// The source of timestamps for relative slots
	pub babe_link: BabeLink<B>,

	/// The proportion of the slot dedicated to proposing.
	///
	/// The block proposing will be limited to this proportion of the slot from the starting of the
	/// slot. However, the proposing can still take longer when there is some lenience factor
	/// applied, because there were no blocks produced for some slots.
	pub block_proposal_slot_portion: SlotProportion,

	/// The maximum proportion of the slot dedicated to proposing with any lenience factor applied
	/// due to no blocks being produced.
	pub max_block_proposal_slot_portion: Option<SlotProportion>,

	/// Handle use to report telemetries.
	pub telemetry: Option<TelemetryHandle>,
}

/// Start the babe worker.
pub fn start_babe<B, C, SC, E, I, SO, CIDP, BS, L, Error>(
	BabeParams {
		keystore,
		client,
		select_chain,
		env,
		block_import,
		sync_oracle,
		justification_sync_link,
		create_inherent_data_providers,
		force_authoring,
		backoff_authoring_blocks,
		babe_link,
		block_proposal_slot_portion,
		max_block_proposal_slot_portion,
		telemetry,
	}: BabeParams<B, C, SC, E, I, SO, L, CIDP, BS>,
) -> Result<BabeWorker<B>, sp_consensus::Error>
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
	C::Api: BabeApi<B>,
	SC: SelectChain<B> + 'static,
	E: Environment<B, Error = Error> + Send + Sync + 'static,
	E::Proposer: Proposer<B, Error = Error, Transaction = sp_api::TransactionFor<C, B>>,
	I: BlockImport<B, Error = ConsensusError, Transaction = sp_api::TransactionFor<C, B>>
		+ Send
		+ Sync
		+ 'static,
	SO: SyncOracle + Send + Sync + Clone + 'static,
	L: sc_consensus::JustificationSyncLink<B> + 'static,
	CIDP: CreateInherentDataProviders<B, ()> + Send + Sync + 'static,
	CIDP::InherentDataProviders: InherentDataProviderExt + Send,
	BS: BackoffAuthoringBlocksStrategy<NumberFor<B>> + Send + Sync + 'static,
	Error: std::error::Error + Send + From<ConsensusError> + From<I::Error> + 'static,
{
	const HANDLE_BUFFER_SIZE: usize = 1024;

	let slot_notification_sinks = Arc::new(Mutex::new(Vec::new()));

	let worker = BabeSlotWorker {
		client: client.clone(),
		block_import,
		env,
		sync_oracle: sync_oracle.clone(),
		justification_sync_link,
		force_authoring,
		backoff_authoring_blocks,
		keystore,
		epoch_changes: babe_link.epoch_changes.clone(),
		slot_notification_sinks: slot_notification_sinks.clone(),
		config: babe_link.config.clone(),
		block_proposal_slot_portion,
		max_block_proposal_slot_portion,
		telemetry,
	};

	info!(target: "babe", "👶 Starting BABE Authorship worker");

	let slot_worker = sc_consensus_slots::start_slot_worker(
		babe_link.config.slot_duration(),
		select_chain,
		sc_consensus_slots::SimpleSlotWorkerToSlotWorker(worker),
		sync_oracle,
		create_inherent_data_providers,
	);

	let (worker_tx, worker_rx) = channel(HANDLE_BUFFER_SIZE);

	let answer_requests =
		answer_requests(worker_rx, babe_link.config, client, babe_link.epoch_changes);

	let inner = future::select(Box::pin(slot_worker), Box::pin(answer_requests));
	Ok(BabeWorker {
		inner: Box::pin(inner.map(|_| ())),
		slot_notification_sinks,
		handle: BabeWorkerHandle(worker_tx),
	})
}

// Remove obsolete block's weight data by leveraging finality notifications.
// This includes data for all finalized blocks (excluding the most recent one)
// and all stale branches.
fn aux_storage_cleanup<C: HeaderMetadata<Block> + HeaderBackend<Block>, Block: BlockT>(
	client: &C,
	notification: &FinalityNotification<Block>,
) -> AuxDataOperations {
	let mut aux_keys = HashSet::new();

	let first = notification.tree_route.first().unwrap_or(&notification.hash);
	match client.header_metadata(*first) {
		Ok(meta) => {
			aux_keys.insert(aux_schema::block_weight_key(meta.parent));
		},
		Err(err) => warn!(
			target: "babe",
			"Failed to lookup metadata for block `{:?}`: {}",
			first,
			err,
		),
	}

	// Cleans data for finalized block's ancestors
	aux_keys.extend(
		notification
			.tree_route
			.iter()
			// Ensure we don't prune latest finalized block.
			// This should not happen, but better be safe than sorry!
			.filter(|h| **h != notification.hash)
			.map(aux_schema::block_weight_key),
	);

	// Cleans data for stale branches.

	for head in notification.stale_heads.iter() {
		let mut hash = *head;
		// Insert stale blocks hashes until canonical chain is reached.
		// If we reach a block that is already part of the `aux_keys` we can stop the processing the
		// head.
		while aux_keys.insert(aux_schema::block_weight_key(hash)) {
			match client.header_metadata(hash) {
				Ok(meta) => {
					hash = meta.parent;

					// If the parent is part of the canonical chain or there doesn't exist a block
					// hash for the parent number (bug?!), we can abort adding blocks.
					if client
						.hash(meta.number.saturating_sub(1u32.into()))
						.ok()
						.flatten()
						.map_or(true, |h| h == hash)
					{
						break
					}
				},
				Err(err) => {
					warn!(
						target: "babe",
						"Header lookup fail while cleaning data for block {:?}: {}",
						hash,
						err,
					);
					break
				},
			}
		}
	}

	aux_keys.into_iter().map(|val| (val, None)).collect()
}

async fn answer_requests<B: BlockT, C>(
	mut request_rx: Receiver<BabeRequest<B>>,
	config: BabeConfiguration,
	client: Arc<C>,
	epoch_changes: SharedEpochChanges<B, Epoch>,
) where
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
			BabeRequest::EpochForChild(parent_hash, parent_number, slot_number, response) => {
				let lookup = || {
					let epoch_changes = epoch_changes.shared_data();
					let epoch_descriptor = epoch_changes
						.epoch_descriptor_for_child_of(
							descendent_query(&*client),
							&parent_hash,
							parent_number,
							slot_number,
						)
						.map_err(|e| Error::<B>::ForkTree(Box::new(e)))?
						.ok_or(Error::<B>::FetchEpoch(parent_hash))?;

					let viable_epoch = epoch_changes
						.viable_epoch(&epoch_descriptor, |slot| Epoch::genesis(&config, slot))
						.ok_or(Error::<B>::FetchEpoch(parent_hash))?;

					Ok(sp_consensus_babe::Epoch {
						epoch_index: viable_epoch.as_ref().epoch_index,
						start_slot: viable_epoch.as_ref().start_slot,
						duration: viable_epoch.as_ref().duration,
						authorities: viable_epoch.as_ref().authorities.clone(),
						randomness: viable_epoch.as_ref().randomness,
						config: viable_epoch.as_ref().config.clone(),
					})
				};

				let _ = response.send(lookup());
			},
		}
	}
}

/// Requests to the BABE service.
#[non_exhaustive]
pub enum BabeRequest<B: BlockT> {
	/// Request the epoch that a child of the given block, with the given slot number would have.
	///
	/// The parent block is identified by its hash and number.
	EpochForChild(
		B::Hash,
		NumberFor<B>,
		Slot,
		oneshot::Sender<Result<sp_consensus_babe::Epoch, Error<B>>>,
	),
}

/// A handle to the BABE worker for issuing requests.
#[derive(Clone)]
pub struct BabeWorkerHandle<B: BlockT>(Sender<BabeRequest<B>>);

impl<B: BlockT> BabeWorkerHandle<B> {
	/// Send a request to the BABE service.
	pub async fn send(&mut self, request: BabeRequest<B>) {
		// Failure to send means that the service is down.
		// This will manifest as the receiver of the request being dropped.
		let _ = self.0.send(request).await;
	}
}

/// Worker for Babe which implements `Future<Output=()>`. This must be polled.
#[must_use]
pub struct BabeWorker<B: BlockT> {
	inner: Pin<Box<dyn Future<Output = ()> + Send + 'static>>,
	slot_notification_sinks: SlotNotificationSinks<B>,
	handle: BabeWorkerHandle<B>,
}

impl<B: BlockT> BabeWorker<B> {
	/// Return an event stream of notifications for when new slot happens, and the corresponding
	/// epoch descriptor.
	pub fn slot_notification_stream(
		&self,
	) -> Receiver<(Slot, ViableEpochDescriptor<B::Hash, NumberFor<B>, Epoch>)> {
		const CHANNEL_BUFFER_SIZE: usize = 1024;

		let (sink, stream) = channel(CHANNEL_BUFFER_SIZE);
		self.slot_notification_sinks.lock().push(sink);
		stream
	}

	/// Get a handle to the worker.
	pub fn handle(&self) -> BabeWorkerHandle<B> {
		self.handle.clone()
	}
}

impl<B: BlockT> Future for BabeWorker<B> {
	type Output = ();

	fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		self.inner.as_mut().poll(cx)
	}
}

/// Slot notification sinks.
type SlotNotificationSinks<B> = Arc<
	Mutex<Vec<Sender<(Slot, ViableEpochDescriptor<<B as BlockT>::Hash, NumberFor<B>, Epoch>)>>>,
>;

struct BabeSlotWorker<B: BlockT, C, E, I, SO, L, BS> {
	client: Arc<C>,
	block_import: I,
	env: E,
	sync_oracle: SO,
	justification_sync_link: L,
	force_authoring: bool,
	backoff_authoring_blocks: Option<BS>,
	keystore: SyncCryptoStorePtr,
	epoch_changes: SharedEpochChanges<B, Epoch>,
	slot_notification_sinks: SlotNotificationSinks<B>,
	config: BabeConfiguration,
	block_proposal_slot_portion: SlotProportion,
	max_block_proposal_slot_portion: Option<SlotProportion>,
	telemetry: Option<TelemetryHandle>,
}

#[async_trait::async_trait]
impl<B, C, E, I, Error, SO, L, BS> sc_consensus_slots::SimpleSlotWorker<B>
	for BabeSlotWorker<B, C, E, I, SO, L, BS>
where
	B: BlockT,
	C: ProvideRuntimeApi<B> + HeaderBackend<B> + HeaderMetadata<B, Error = ClientError>,
	C::Api: BabeApi<B>,
	E: Environment<B, Error = Error> + Sync,
	E::Proposer: Proposer<B, Error = Error, Transaction = sp_api::TransactionFor<C, B>>,
	I: BlockImport<B, Transaction = sp_api::TransactionFor<C, B>> + Send + Sync + 'static,
	SO: SyncOracle + Send + Clone + Sync,
	L: sc_consensus::JustificationSyncLink<B>,
	BS: BackoffAuthoringBlocksStrategy<NumberFor<B>> + Sync,
	Error: std::error::Error + Send + From<ConsensusError> + From<I::Error> + 'static,
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
		"babe"
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
			.viable_epoch(epoch_descriptor, |slot| Epoch::genesis(&self.config, slot))
			.map(|epoch| epoch.as_ref().authorities.len())
	}

	async fn claim_slot(
		&self,
		_parent_header: &B::Header,
		slot: Slot,
		epoch_descriptor: &ViableEpochDescriptor<B::Hash, NumberFor<B>, Epoch>,
	) -> Option<Self::Claim> {
		debug!(target: "babe", "Attempting to claim slot {}", slot);
		let s = authorship::claim_slot(
			slot,
			self.epoch_changes
				.shared_data()
				.viable_epoch(epoch_descriptor, |slot| Epoch::genesis(&self.config, slot))?
				.as_ref(),
			&self.keystore,
		);

		if s.is_some() {
			debug!(target: "babe", "Claimed slot {}", slot);
		}

		s
	}

	fn notify_slot(
		&self,
		_parent_header: &B::Header,
		slot: Slot,
		epoch_descriptor: &ViableEpochDescriptor<B::Hash, NumberFor<B>, Epoch>,
	) {
		let sinks = &mut self.slot_notification_sinks.lock();
		sinks.retain_mut(|sink| match sink.try_send((slot, epoch_descriptor.clone())) {
			Ok(()) => true,
			Err(e) =>
				if e.is_full() {
					warn!(target: "babe", "Trying to notify a slot but the channel is full");
					true
				} else {
					false
				},
		});
	}

	fn pre_digest_data(&self, _slot: Slot, claim: &Self::Claim) -> Vec<sp_runtime::DigestItem> {
		vec![<DigestItem as CompatibleDigestItem>::babe_pre_digest(claim.0.clone())]
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
		// sign the pre-sealed hash of the block and then
		// add it to a digest item.
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
		let digest_item = <DigestItem as CompatibleDigestItem>::babe_seal(signature);

		let mut import_block = BlockImportParams::new(BlockOrigin::Own, header);
		import_block.post_digests.push(digest_item);
		import_block.body = Some(body);
		import_block.state_action =
			StateAction::ApplyChanges(sc_consensus::StorageChanges::Changes(storage_changes));
		import_block
			.insert_intermediate(INTERMEDIATE_KEY, BabeIntermediate::<B> { epoch_descriptor });

		Ok(import_block)
	}

	fn force_authoring(&self) -> bool {
		self.force_authoring
	}

	fn should_backoff(&self, slot: Slot, chain_head: &B::Header) -> bool {
		if let Some(ref strategy) = self.backoff_authoring_blocks {
			if let Ok(chain_head_slot) =
				find_pre_digest::<B>(chain_head).map(|digest| digest.slot())
			{
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
		Box::pin(
			self.env
				.init(block)
				.map_err(|e| sp_consensus::Error::ClientImport(format!("{:?}", e))),
		)
	}

	fn telemetry(&self) -> Option<TelemetryHandle> {
		self.telemetry.clone()
	}

	fn proposing_remaining_duration(&self, slot_info: &SlotInfo<B>) -> Duration {
		let parent_slot = find_pre_digest::<B>(&slot_info.chain_head).ok().map(|d| d.slot());

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

/// Extract the BABE pre digest from the given header. Pre-runtime digests are
/// mandatory, the function will return `Err` if none is found.
pub fn find_pre_digest<B: BlockT>(header: &B::Header) -> Result<PreDigest, Error<B>> {
	// genesis block doesn't contain a pre digest so let's generate a
	// dummy one to not break any invariants in the rest of the code
	if header.number().is_zero() {
		return Ok(PreDigest::SecondaryPlain(SecondaryPlainPreDigest {
			slot: 0.into(),
			authority_index: 0,
		}))
	}

	let mut pre_digest: Option<_> = None;
	for log in header.digest().logs() {
		trace!(target: "babe", "Checking log {:?}, looking for pre runtime digest", log);
		match (log.as_babe_pre_digest(), pre_digest.is_some()) {
			(Some(_), true) => return Err(babe_err(Error::MultiplePreRuntimeDigests)),
			(None, _) => trace!(target: "babe", "Ignoring digest not meant for us"),
			(s, false) => pre_digest = s,
		}
	}
	pre_digest.ok_or_else(|| babe_err(Error::NoPreRuntimeDigest))
}

/// Extract the BABE epoch change digest from the given header, if it exists.
fn find_next_epoch_digest<B: BlockT>(
	header: &B::Header,
) -> Result<Option<NextEpochDescriptor>, Error<B>> {
	let mut epoch_digest: Option<_> = None;
	for log in header.digest().logs() {
		trace!(target: "babe", "Checking log {:?}, looking for epoch change digest.", log);
		let log = log.try_to::<ConsensusLog>(OpaqueDigestItemId::Consensus(&BABE_ENGINE_ID));
		match (log, epoch_digest.is_some()) {
			(Some(ConsensusLog::NextEpochData(_)), true) =>
				return Err(babe_err(Error::MultipleEpochChangeDigests)),
			(Some(ConsensusLog::NextEpochData(epoch)), false) => epoch_digest = Some(epoch),
			_ => trace!(target: "babe", "Ignoring digest not meant for us"),
		}
	}

	Ok(epoch_digest)
}

/// Extract the BABE config change digest from the given header, if it exists.
fn find_next_config_digest<B: BlockT>(
	header: &B::Header,
) -> Result<Option<NextConfigDescriptor>, Error<B>> {
	let mut config_digest: Option<_> = None;
	for log in header.digest().logs() {
		trace!(target: "babe", "Checking log {:?}, looking for epoch change digest.", log);
		let log = log.try_to::<ConsensusLog>(OpaqueDigestItemId::Consensus(&BABE_ENGINE_ID));
		match (log, config_digest.is_some()) {
			(Some(ConsensusLog::NextConfigData(_)), true) =>
				return Err(babe_err(Error::MultipleConfigChangeDigests)),
			(Some(ConsensusLog::NextConfigData(config)), false) => config_digest = Some(config),
			_ => trace!(target: "babe", "Ignoring digest not meant for us"),
		}
	}

	Ok(config_digest)
}

/// State that must be shared between the import queue and the authoring logic.
#[derive(Clone)]
pub struct BabeLink<Block: BlockT> {
	epoch_changes: SharedEpochChanges<Block, Epoch>,
	config: BabeConfiguration,
}

impl<Block: BlockT> BabeLink<Block> {
	/// Get the epoch changes of this link.
	pub fn epoch_changes(&self) -> &SharedEpochChanges<Block, Epoch> {
		&self.epoch_changes
	}

	/// Get the config of this link.
	pub fn config(&self) -> &BabeConfiguration {
		&self.config
	}
}

/// A verifier for Babe blocks.
pub struct BabeVerifier<Block: BlockT, Client, SelectChain, CIDP> {
	client: Arc<Client>,
	select_chain: SelectChain,
	create_inherent_data_providers: CIDP,
	config: BabeConfiguration,
	epoch_changes: SharedEpochChanges<Block, Epoch>,
	telemetry: Option<TelemetryHandle>,
}

impl<Block, Client, SelectChain, CIDP> BabeVerifier<Block, Client, SelectChain, CIDP>
where
	Block: BlockT,
	Client: AuxStore + HeaderBackend<Block> + HeaderMetadata<Block> + ProvideRuntimeApi<Block>,
	Client::Api: BlockBuilderApi<Block> + BabeApi<Block>,
	SelectChain: sp_consensus::SelectChain<Block>,
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
		// don't report any equivocations during initial sync
		// as they are most likely stale.
		if *origin == BlockOrigin::NetworkInitialSync {
			return Ok(())
		}

		// check if authorship of this header is an equivocation and return a proof if so.
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

		// get the best block on which we will build and send the equivocation report.
		let best_id = self
			.select_chain
			.best_chain()
			.await
			.map(|h| BlockId::Hash(h.hash()))
			.map_err(|e| Error::Client(e.into()))?;

		// generate a key ownership proof. we start by trying to generate the
		// key owernship proof at the parent of the equivocating header, this
		// will make sure that proof generation is successful since it happens
		// during the on-going session (i.e. session keys are available in the
		// state to be able to generate the proof). this might fail if the
		// equivocation happens on the first block of the session, in which case
		// its parent would be on the previous session. if generation on the
		// parent header fails we try with best block as well.
		let generate_key_owner_proof = |block_id: &BlockId<Block>| {
			self.client
				.runtime_api()
				.generate_key_ownership_proof(block_id, slot, equivocation_proof.offender.clone())
				.map_err(Error::RuntimeApi)
		};

		let parent_id = BlockId::Hash(*header.parent_hash());
		let key_owner_proof = match generate_key_owner_proof(&parent_id)? {
			Some(proof) => proof,
			None => match generate_key_owner_proof(&best_id)? {
				Some(proof) => proof,
				None => {
					debug!(target: "babe", "Equivocation offender is not part of the authority set.");
					return Ok(())
				},
			},
		};

		// submit equivocation report at best block.
		self.client
			.runtime_api()
			.submit_report_equivocation_unsigned_extrinsic(
				&best_id,
				equivocation_proof,
				key_owner_proof,
			)
			.map_err(Error::RuntimeApi)?;

		info!(target: "babe", "Submitted equivocation report for author {:?}", author);

		Ok(())
	}
}

type BlockVerificationResult<Block> =
	Result<(BlockImportParams<Block, ()>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String>;

#[async_trait::async_trait]
impl<Block, Client, SelectChain, CIDP> Verifier<Block>
	for BabeVerifier<Block, Client, SelectChain, CIDP>
where
	Block: BlockT,
	Client: HeaderMetadata<Block, Error = sp_blockchain::Error>
		+ HeaderBackend<Block>
		+ ProvideRuntimeApi<Block>
		+ Send
		+ Sync
		+ AuxStore,
	Client::Api: BlockBuilderApi<Block> + BabeApi<Block>,
	SelectChain: sp_consensus::SelectChain<Block>,
	CIDP: CreateInherentDataProviders<Block, ()> + Send + Sync,
	CIDP::InherentDataProviders: InherentDataProviderExt + Send + Sync,
{
	async fn verify(
		&mut self,
		mut block: BlockImportParams<Block, ()>,
	) -> BlockVerificationResult<Block> {
		trace!(
			target: "babe",
			"Verifying origin: {:?} header: {:?} justification(s): {:?} body: {:?}",
			block.origin,
			block.header,
			block.justifications,
			block.body,
		);

		let hash = block.header.hash();
		let parent_hash = *block.header.parent_hash();

		if block.with_state() {
			// When importing whole state we don't calculate epoch descriptor, but rather
			// read it from the state after import. We also skip all verifications
			// because there's no parent state and we trust the sync module to verify
			// that the state is correct and finalized.
			return Ok((block, Default::default()))
		}

		debug!(target: "babe", "We have {:?} logs in this header", block.header.digest().logs().len());

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
				.viable_epoch(&epoch_descriptor, |slot| Epoch::genesis(&self.config, slot))
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

		match check_header {
			CheckedHeader::Checked(pre_header, verified_info) => {
				let babe_pre_digest = verified_info
					.pre_digest
					.as_babe_pre_digest()
					.expect("check_header always returns a pre-digest digest item; qed");
				let slot = babe_pre_digest.slot();

				// the header is valid but let's check if there was something else already
				// proposed at the same slot by the given author. if there was, we will
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
					warn!(target: "babe", "Error checking/reporting BABE equivocation: {}", err);
				}

				if let Some(inner_body) = block.body {
					let new_block = Block::new(pre_header.clone(), inner_body);
					if !block.state_action.skip_execution_checks() {
						// if the body is passed through and the block was executed,
						// we need to use the runtime to check that the internally-set
						// timestamp in the inherents actually matches the slot set in the seal.
						let mut inherent_data = create_inherent_data_providers
							.create_inherent_data()
							.map_err(Error::<Block>::CreateInherents)?;
						inherent_data.babe_replace_inherent_data(slot);

						self.check_inherents(
							new_block.clone(),
							BlockId::Hash(parent_hash),
							inherent_data,
							create_inherent_data_providers,
							block.origin.into(),
						)
						.await?;
					}

					let (_, inner_body) = new_block.deconstruct();
					block.body = Some(inner_body);
				}

				trace!(target: "babe", "Checked {:?}; importing.", pre_header);
				telemetry!(
					self.telemetry;
					CONSENSUS_TRACE;
					"babe.checked_and_importing";
					"pre_header" => ?pre_header,
				);

				block.header = pre_header;
				block.post_digests.push(verified_info.seal);
				block.insert_intermediate(
					INTERMEDIATE_KEY,
					BabeIntermediate::<Block> { epoch_descriptor },
				);
				block.post_hash = Some(hash);

				Ok((block, Default::default()))
			},
			CheckedHeader::Deferred(a, b) => {
				debug!(target: "babe", "Checking {:?} failed; {:?}, {:?}.", hash, a, b);
				telemetry!(
					self.telemetry;
					CONSENSUS_DEBUG;
					"babe.header_too_far_in_future";
					"hash" => ?hash, "a" => ?a, "b" => ?b
				);
				Err(Error::<Block>::TooFarInFuture(hash).into())
			},
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
pub struct BabeBlockImport<Block: BlockT, Client, I> {
	inner: I,
	client: Arc<Client>,
	epoch_changes: SharedEpochChanges<Block, Epoch>,
	config: BabeConfiguration,
}

impl<Block: BlockT, I: Clone, Client> Clone for BabeBlockImport<Block, Client, I> {
	fn clone(&self) -> Self {
		BabeBlockImport {
			inner: self.inner.clone(),
			client: self.client.clone(),
			epoch_changes: self.epoch_changes.clone(),
			config: self.config.clone(),
		}
	}
}

impl<Block: BlockT, Client, I> BabeBlockImport<Block, Client, I> {
	fn new(
		client: Arc<Client>,
		epoch_changes: SharedEpochChanges<Block, Epoch>,
		block_import: I,
		config: BabeConfiguration,
	) -> Self {
		BabeBlockImport { client, inner: block_import, epoch_changes, config }
	}
}

impl<Block, Client, Inner> BabeBlockImport<Block, Client, Inner>
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
	Client::Api: BabeApi<Block> + ApiExt<Block>,
{
	/// Import whole state after warp sync.
	// This function makes multiple transactions to the DB. If one of them fails we may
	// end up in an inconsistent state and have to resync.
	async fn import_state(
		&mut self,
		mut block: BlockImportParams<Block, sp_api::TransactionFor<Client, Block>>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
	) -> Result<ImportResult, ConsensusError> {
		let hash = block.post_hash();
		let parent_hash = *block.header.parent_hash();
		let number = *block.header.number();

		block.fork_choice = Some(ForkChoiceStrategy::Custom(true));
		// Reset block weight.
		aux_schema::write_block_weight(hash, 0, |values| {
			block
				.auxiliary
				.extend(values.iter().map(|(k, v)| (k.to_vec(), Some(v.to_vec()))))
		});

		// First make the client import the state.
		let import_result = self.inner.import_block(block, new_cache).await;
		let aux = match import_result {
			Ok(ImportResult::Imported(aux)) => aux,
			Ok(r) =>
				return Err(ConsensusError::ClientImport(format!(
					"Unexpected import result: {:?}",
					r
				))),
			Err(r) => return Err(r.into()),
		};

		// Read epoch info from the imported state.
		let block_id = BlockId::hash(hash);
		let current_epoch = self.client.runtime_api().current_epoch(&block_id).map_err(|e| {
			ConsensusError::ClientImport(babe_err::<Block>(Error::RuntimeApi(e)).into())
		})?;
		let next_epoch = self.client.runtime_api().next_epoch(&block_id).map_err(|e| {
			ConsensusError::ClientImport(babe_err::<Block>(Error::RuntimeApi(e)).into())
		})?;

		let mut epoch_changes = self.epoch_changes.shared_data_locked();
		epoch_changes.reset(parent_hash, hash, number, current_epoch.into(), next_epoch.into());
		aux_schema::write_epoch_changes::<Block, _, _>(&*epoch_changes, |insert| {
			self.client.insert_aux(insert, [])
		})
		.map_err(|e| ConsensusError::ClientImport(e.to_string()))?;

		Ok(ImportResult::Imported(aux))
	}
}

#[async_trait::async_trait]
impl<Block, Client, Inner> BlockImport<Block> for BabeBlockImport<Block, Client, Inner>
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
	Client::Api: BabeApi<Block> + ApiExt<Block>,
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

		// early exit if block already in chain, otherwise the check for
		// epoch changes will error when trying to re-import an epoch change
		match self.client.status(BlockId::Hash(hash)) {
			Ok(sp_blockchain::BlockStatus::InChain) => {
				// When re-importing existing block strip away intermediates.
				let _ = block.remove_intermediate::<BabeIntermediate<Block>>(INTERMEDIATE_KEY);
				block.fork_choice = Some(ForkChoiceStrategy::Custom(false));
				return self.inner.import_block(block, new_cache).await.map_err(Into::into)
			},
			Ok(sp_blockchain::BlockStatus::Unknown) => {},
			Err(e) => return Err(ConsensusError::ClientImport(e.to_string())),
		}

		if block.with_state() {
			return self.import_state(block, new_cache).await
		}

		let pre_digest = find_pre_digest::<Block>(&block.header).expect(
			"valid babe headers must contain a predigest; header has been already verified; qed",
		);
		let slot = pre_digest.slot();

		let parent_hash = *block.header.parent_hash();
		let parent_header = self
			.client
			.header(BlockId::Hash(parent_hash))
			.map_err(|e| ConsensusError::ChainLookup(e.to_string()))?
			.ok_or_else(|| {
				ConsensusError::ChainLookup(
					babe_err(Error::<Block>::ParentUnavailable(parent_hash, hash)).into(),
				)
			})?;

		let parent_slot = find_pre_digest::<Block>(&parent_header).map(|d| d.slot()).expect(
			"parent is non-genesis; valid BABE headers contain a pre-digest; header has already \
			 been verified; qed",
		);

		// make sure that slot number is strictly increasing
		if slot <= parent_slot {
			return Err(ConsensusError::ClientImport(
				babe_err(Error::<Block>::SlotMustIncrease(parent_slot, slot)).into(),
			))
		}

		// if there's a pending epoch we'll save the previous epoch changes here
		// this way we can revert it if there's any error
		let mut old_epoch_changes = None;

		// Use an extra scope to make the compiler happy, because otherwise he complains about the
		// mutex, even if we dropped it...
		let mut epoch_changes = {
			let mut epoch_changes = self.epoch_changes.shared_data_locked();

			// check if there's any epoch change expected to happen at this slot.
			// `epoch` is the epoch to verify the block under, and `first_in_epoch` is true
			// if this is the first block in its chain for that epoch.
			//
			// also provides the total weight of the chain, including the imported block.
			let (epoch_descriptor, first_in_epoch, parent_weight) = {
				let parent_weight = if *parent_header.number() == Zero::zero() {
					0
				} else {
					aux_schema::load_block_weight(&*self.client, parent_hash)
						.map_err(|e| ConsensusError::ClientImport(e.to_string()))?
						.ok_or_else(|| {
							ConsensusError::ClientImport(
								babe_err(Error::<Block>::ParentBlockNoAssociatedWeight(hash))
									.into(),
							)
						})?
				};

				let intermediate =
					block.remove_intermediate::<BabeIntermediate<Block>>(INTERMEDIATE_KEY)?;

				let epoch_descriptor = intermediate.epoch_descriptor;
				let first_in_epoch = parent_slot < epoch_descriptor.start_slot();
				(epoch_descriptor, first_in_epoch, parent_weight)
			};

			let total_weight = parent_weight + pre_digest.added_weight();

			// search for this all the time so we can reject unexpected announcements.
			let next_epoch_digest = find_next_epoch_digest::<Block>(&block.header)
				.map_err(|e| ConsensusError::ClientImport(e.to_string()))?;
			let next_config_digest = find_next_config_digest::<Block>(&block.header)
				.map_err(|e| ConsensusError::ClientImport(e.to_string()))?;

			match (first_in_epoch, next_epoch_digest.is_some(), next_config_digest.is_some()) {
				(true, true, _) => {},
				(false, false, false) => {},
				(false, false, true) =>
					return Err(ConsensusError::ClientImport(
						babe_err(Error::<Block>::UnexpectedConfigChange).into(),
					)),
				(true, false, _) =>
					return Err(ConsensusError::ClientImport(
						babe_err(Error::<Block>::ExpectedEpochChange(hash, slot)).into(),
					)),
				(false, true, _) =>
					return Err(ConsensusError::ClientImport(
						babe_err(Error::<Block>::UnexpectedEpochChange).into(),
					)),
			}

			let info = self.client.info();

			if let Some(next_epoch_descriptor) = next_epoch_digest {
				old_epoch_changes = Some((*epoch_changes).clone());

				let viable_epoch = epoch_changes
					.viable_epoch(&epoch_descriptor, |slot| Epoch::genesis(&self.config, slot))
					.ok_or_else(|| {
						ConsensusError::ClientImport(Error::<Block>::FetchEpoch(parent_hash).into())
					})?;

				let epoch_config = next_config_digest
					.map(Into::into)
					.unwrap_or_else(|| viable_epoch.as_ref().config.clone());

				// restrict info logging during initial sync to avoid spam
				let log_level = if block.origin == BlockOrigin::NetworkInitialSync {
					log::Level::Debug
				} else {
					log::Level::Info
				};

				log!(target: "babe",
					 log_level,
					 "👶 New epoch {} launching at block {} (block slot {} >= start slot {}).",
					 viable_epoch.as_ref().epoch_index,
					 hash,
					 slot,
					 viable_epoch.as_ref().start_slot,
				);

				let next_epoch = viable_epoch.increment((next_epoch_descriptor, epoch_config));

				log!(target: "babe",
					 log_level,
					 "👶 Next epoch starts at slot {}",
					 next_epoch.as_ref().start_slot,
				);

				// prune the tree of epochs not part of the finalized chain or
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
					debug!(target: "babe", "Failed to launch next epoch: {}", e);
					*epoch_changes =
						old_epoch_changes.expect("set `Some` above and not taken; qed");
					return Err(e)
				}

				crate::aux_schema::write_epoch_changes::<Block, _, _>(&*epoch_changes, |insert| {
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

		// revert to the original epoch changes in case there's an error
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
fn prune_finalized<Block, Client>(
	client: Arc<Client>,
	epoch_changes: &mut EpochChangesFor<Block, Epoch>,
) -> Result<(), ConsensusError>
where
	Block: BlockT,
	Client: HeaderBackend<Block> + HeaderMetadata<Block, Error = sp_blockchain::Error>,
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

		find_pre_digest::<Block>(&finalized_header)
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

/// Produce a BABE block-import object to be used later on in the construction of
/// an import-queue.
///
/// Also returns a link object used to correctly instantiate the import queue
/// and background worker.
pub fn block_import<Client, Block: BlockT, I>(
	config: BabeConfiguration,
	wrapped_block_import: I,
	client: Arc<Client>,
) -> ClientResult<(BabeBlockImport<Block, Client, I>, BabeLink<Block>)>
where
	Client: AuxStore
		+ HeaderBackend<Block>
		+ HeaderMetadata<Block, Error = sp_blockchain::Error>
		+ PreCommitActions<Block>
		+ 'static,
{
	let epoch_changes = aux_schema::load_epoch_changes::<Block, _>(&*client, &config)?;
	let link = BabeLink { epoch_changes: epoch_changes.clone(), config: config.clone() };

	// NOTE: this isn't entirely necessary, but since we didn't use to prune the
	// epoch tree it is useful as a migration, so that nodes prune long trees on
	// startup rather than waiting until importing the next epoch change block.
	prune_finalized(client.clone(), &mut epoch_changes.shared_data())?;

	let client_weak = Arc::downgrade(&client);
	let on_finality = move |summary: &FinalityNotification<Block>| {
		if let Some(client) = client_weak.upgrade() {
			aux_storage_cleanup(client.as_ref(), summary)
		} else {
			Default::default()
		}
	};
	client.register_finality_action(Box::new(on_finality));

	let import = BabeBlockImport::new(client, epoch_changes, wrapped_block_import, config);

	Ok((import, link))
}

/// Start an import queue for the BABE consensus algorithm.
///
/// This method returns the import queue, some data that needs to be passed to the block authoring
/// logic (`BabeLink`), and a future that must be run to
/// completion and is responsible for listening to finality notifications and
/// pruning the epoch changes tree.
///
/// The block import object provided must be the `BabeBlockImport` or a wrapper
/// of it, otherwise crucial import logic will be omitted.
pub fn import_queue<Block: BlockT, Client, SelectChain, Inner, CIDP>(
	babe_link: BabeLink<Block>,
	block_import: Inner,
	justification_import: Option<BoxJustificationImport<Block>>,
	client: Arc<Client>,
	select_chain: SelectChain,
	create_inherent_data_providers: CIDP,
	spawner: &impl sp_core::traits::SpawnEssentialNamed,
	registry: Option<&Registry>,
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
	Client::Api: BlockBuilderApi<Block> + BabeApi<Block> + ApiExt<Block>,
	SelectChain: sp_consensus::SelectChain<Block> + 'static,
	CIDP: CreateInherentDataProviders<Block, ()> + Send + Sync + 'static,
	CIDP::InherentDataProviders: InherentDataProviderExt + Send + Sync,
{
	let verifier = BabeVerifier {
		select_chain,
		create_inherent_data_providers,
		config: babe_link.config,
		epoch_changes: babe_link.epoch_changes,
		telemetry,
		client,
	};

	Ok(BasicQueue::new(verifier, Box::new(block_import), justification_import, spawner, registry))
}

/// Reverts protocol aux data to at most the last finalized block.
/// In particular, epoch-changes and block weights announced after the revert
/// point are removed.
pub fn revert<Block, Client, Backend>(
	client: Arc<Client>,
	backend: Arc<Backend>,
	blocks: NumberFor<Block>,
) -> ClientResult<()>
where
	Block: BlockT,
	Client: AuxStore
		+ HeaderMetadata<Block, Error = sp_blockchain::Error>
		+ HeaderBackend<Block>
		+ ProvideRuntimeApi<Block>
		+ UsageProvider<Block>,
	Client::Api: BabeApi<Block>,
	Backend: BackendT<Block>,
{
	let best_number = client.info().best_number;
	let finalized = client.info().finalized_number;

	let revertible = blocks.min(best_number - finalized);
	if revertible == Zero::zero() {
		return Ok(())
	}

	let revert_up_to_number = best_number - revertible;
	let revert_up_to_hash = client.hash(revert_up_to_number)?.ok_or(ClientError::Backend(
		format!("Unexpected hash lookup failure for block number: {}", revert_up_to_number),
	))?;

	// Revert epoch changes tree.

	// This config is only used on-genesis.
	let config = configuration(&*client)?;
	let epoch_changes = aux_schema::load_epoch_changes::<Block, Client>(&*client, &config)?;
	let mut epoch_changes = epoch_changes.shared_data();

	if revert_up_to_number == Zero::zero() {
		// Special case, no epoch changes data were present on genesis.
		*epoch_changes = EpochChangesFor::<Block, Epoch>::default();
	} else {
		epoch_changes.revert(descendent_query(&*client), revert_up_to_hash, revert_up_to_number);
	}

	// Remove block weights added after the revert point.

	let mut weight_keys = HashSet::with_capacity(revertible.saturated_into());

	let leaves = backend.blockchain().leaves()?.into_iter().filter(|&leaf| {
		sp_blockchain::tree_route(&*client, revert_up_to_hash, leaf)
			.map(|route| route.retracted().is_empty())
			.unwrap_or_default()
	});

	for leaf in leaves {
		let mut hash = leaf;
		loop {
			let meta = client.header_metadata(hash)?;
			if meta.number <= revert_up_to_number ||
				!weight_keys.insert(aux_schema::block_weight_key(hash))
			{
				// We've reached the revert point or an already processed branch, stop here.
				break
			}
			hash = meta.parent;
		}
	}

	let weight_keys: Vec<_> = weight_keys.iter().map(|val| val.as_slice()).collect();

	// Write epoch changes and remove weights in one shot.
	aux_schema::write_epoch_changes::<Block, _, _>(&epoch_changes, |values| {
		client.insert_aux(values, weight_keys.iter())
	})
}
