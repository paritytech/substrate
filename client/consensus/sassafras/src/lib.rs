// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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
	collections::HashMap,
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
use log::{debug, info, trace};
use parking_lot::Mutex;
use prometheus_endpoint::Registry;
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
	descendent_query, Epoch as EpochT, EpochChangesFor, SharedEpochChanges, ViableEpochDescriptor,
};
use sc_consensus_slots::{
	check_equivocation, BackoffAuthoringBlocksStrategy, CheckedHeader, InherentDataProviderExt,
	SlotInfo, StorageChanges,
};
use sc_telemetry::{telemetry, TelemetryHandle, CONSENSUS_DEBUG, CONSENSUS_INFO, CONSENSUS_WARN};
use sp_api::{ApiExt, ProvideRuntimeApi};
use sp_block_builder::BlockBuilder as BlockBuilderApi;
use sp_blockchain::{
	Backend as _, Error as ClientError, HeaderBackend, HeaderMetadata, Result as ClientResult,
};
use sp_consensus::{
	BlockOrigin, CacheKeyId, CanAuthorWith, Environment, Error as ConsensusError, Proposer,
	SelectChain,
};
use sp_consensus_sassafras::inherents::SassafrasInherentData;
use sp_consensus_slots::{Slot, SlotDuration};
use sp_core::traits::SpawnEssentialNamed;
use sp_inherents::{CreateInherentDataProviders, InherentData, InherentDataProvider};
use sp_runtime::{
	generic::{BlockId, OpaqueDigestItemId},
	traits::{Block as BlockT, Header, NumberFor, One, SaturatedConversion, Saturating, Zero},
	DigestItem,
};

pub use sp_consensus::SyncOracle;
pub use sp_consensus_sassafras::{
	digests::{NextEpochDescriptor, PreDigest},
	AuthorityId, AuthorityPair, AuthoritySignature, SassafrasApi, SassafrasEpochConfiguration,
	SassafrasGenesisConfiguration,
};

pub mod aux_schema;

/// Sassafras epoch information
#[derive(Decode, Encode, PartialEq, Eq, Clone, Debug)]
pub struct Epoch {
	/// The starting slot of the epoch.
	pub start_slot: Slot,
	/// The duration of this epoch.
	pub duration: u64,
	// TODO-SASS
}

impl EpochT for Epoch {
	type NextEpochDescriptor = NextEpochDescriptor;
	type Slot = Slot;

	fn increment(&self, _descriptor: NextEpochDescriptor) -> Epoch {
		// TODO-SASS
		Epoch { start_slot: self.start_slot + self.duration, duration: self.duration }
	}

	fn start_slot(&self) -> Slot {
		self.start_slot
	}

	fn end_slot(&self) -> Slot {
		self.start_slot + self.duration
	}
}

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
		trace!(target: "sassafras", "Getting configuration");

		let mut best_block_id = BlockId::Hash(client.usage_info().chain.best_hash);
		if client.usage_info().chain.finalized_state.is_none() {
			debug!(target: "sassafras", "No finalized state is available. Reading config from genesis");
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
	/// The chain selection strategy
	pub select_chain: SC,
	/// The environment we are producing blocks for.
	pub env: EN,
	/// The underlying block-import object to supply our produced blocks to.
	/// This must be a `SassafrasBlockImport` or a wrapper of it, otherwise
	/// critical consensus logic will be omitted.
	pub block_import: I,
	/// The source of timestamps for relative slots
	pub sassafras_link: SassafrasLink<B>,
	/// A sync oracle
	pub sync_oracle: SO,
	/// Hook into the sync module to control the justification sync process.
	pub justification_sync_link: L,
	/// Something that can create the inherent data providers.
	pub create_inherent_data_providers: CIDP,
	/// Checks if the current native implementation can author with a runtime at a given block.
	pub can_author_with: CAW,
	// TODO-SASS
}

/// Start the Sassafras worker.
pub fn start_sassafras<B, C, SC, EN, I, SO, CIDP, CAW, L, ER>(
	SassafrasParams {
		client,
		select_chain,
		env,
		block_import,
		sassafras_link,
		sync_oracle,
		justification_sync_link,
		create_inherent_data_providers,
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
	info!(target: "sassafras", "🍁 Starting Sassafras Authorship worker");

	let slot_notification_sinks = Arc::new(Mutex::new(Vec::new()));

	let worker = SassafrasSlotWorker {
		client: client.clone(),
		block_import,
		env,
		sync_oracle: sync_oracle.clone(),
		justification_sync_link,
		epoch_changes: sassafras_link.epoch_changes.clone(),
		slot_notification_sinks: slot_notification_sinks.clone(),
		config: sassafras_link.config.clone(),
	};

	let slot_worker = sc_consensus_slots::start_slot_worker(
		sassafras_link.config.slot_duration(),
		select_chain,
		sc_consensus_slots::SimpleSlotWorkerToSlotWorker(worker),
		sync_oracle,
		create_inherent_data_providers,
		can_author_with,
	);

	// TODO-SASS: proper handler for inbound requests
	let answer_requests = answer_requests();

	let inner = future::select(Box::pin(slot_worker), Box::pin(answer_requests));
	Ok(SassafrasWorker { inner: Box::pin(inner.map(|_| ())), slot_notification_sinks })
}

async fn answer_requests() {
	futures::pending!()
}

/// Worker for Sassafras which implements `Future<Output=()>`. This must be polled.
#[must_use]
pub struct SassafrasWorker<B: BlockT> {
	inner: Pin<Box<dyn Future<Output = ()> + Send + 'static>>,
	slot_notification_sinks: SlotNotificationSinks<B>,
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
	epoch_changes: SharedEpochChanges<B, Epoch>,
	slot_notification_sinks: SlotNotificationSinks<B>,
	// TODO-SASS (will be used by authorities_len method)
	#[allow(dead_code)]
	config: Config,
}

#[async_trait::async_trait]
impl<B, C, E, I, ER, SO, L> sc_consensus_slots::SimpleSlotWorker<B>
	for SassafrasSlotWorker<B, C, E, I, SO, L>
where
	B: BlockT,
	C: ProvideRuntimeApi<B> + HeaderBackend<B> + HeaderMetadata<B, Error = ClientError>,
	//C::Api: SassafrasApi<B>, // TODO-SASS ?
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

	fn authorities_len(&self, _epoch_descriptor: &Self::EpochData) -> Option<usize> {
		//TODO-SASS
		// self.epoch_changes
		// 	.shared_data()
		// 	.viable_epoch(epoch_descriptor, |slot| {
		// 		Epoch::genesis(&self.config.genesis_config, slot)
		// 	})
		// 	.map(|epoch| epoch.as_ref().authorities.len())
		None
	}

	async fn claim_slot(
		&self,
		_parent_header: &B::Header,
		slot: Slot,
		_epoch_descriptor: &ViableEpochDescriptor<B::Hash, NumberFor<B>, Epoch>,
	) -> Option<Self::Claim> {
		debug!(target: "sassafras", "Attempting to claim slot {}", slot);
		// TODO-SASS
		None
	}

	fn notify_slot(
		&self,
		_parent_header: &B::Header,
		_slot: Slot,
		_epoch_descriptor: &ViableEpochDescriptor<B::Hash, NumberFor<B>, Epoch>,
	) {
		// TODO-SASS
		// RetainMut::retain_mut(&mut *self.slot_notification_sinks.lock(), |sink| {
		// 	match sink.try_send((slot, epoch_descriptor.clone())) {
		// 		Ok(()) => true,
		// 		Err(e) =>
		// 			if e.is_full() {
		// 				warn!(target: "sassafras", "Trying to notify a slot but the channel is full");
		// 				true
		// 			} else {
		// 				false
		// 			},
		// 	}
		// });
	}

	fn pre_digest_data(&self, _slot: Slot, _claim: &Self::Claim) -> Vec<sp_runtime::DigestItem> {
		// TODO-SASS
		//vec![<DigestItem as CompatibleDigestItem>::sassafras_pre_digest(claim.0.clone())]
		vec![]
	}

	async fn block_import_params(
		&self,
		header: B::Header,
		_header_hash: &B::Hash,
		_body: Vec<B::Extrinsic>,
		_storage_changes: StorageChanges<<Self::BlockImport as BlockImport<B>>::Transaction, B>,
		(_, _public): Self::Claim,
		_epoch_descriptor: Self::EpochData,
	) -> Result<
		sc_consensus::BlockImportParams<B, <Self::BlockImport as BlockImport<B>>::Transaction>,
		sp_consensus::Error,
	> {
		// // sign the pre-sealed hash of the block and then
		// // add it to a digest item.
		// let public_type_pair = public.clone().into();
		// let public = public.to_raw_vec();
		// let signature = SyncCryptoStore::sign_with(
		// 	&*self.keystore,
		// 	<AuthorityId as AppKey>::ID,
		// 	&public_type_pair,
		// 	header_hash.as_ref(),
		// )
		// .map_err(|e| sp_consensus::Error::CannotSign(public.clone(), e.to_string()))?
		// .ok_or_else(|| {
		// 	sp_consensus::Error::CannotSign(
		// 		public.clone(),
		// 		"Could not find key in keystore.".into(),
		// 	)
		// })?;
		// let signature: AuthoritySignature = signature
		// 	.clone()
		// 	.try_into()
		// 	.map_err(|_| sp_consensus::Error::InvalidSignature(signature, public))?;
		// let digest_item = <DigestItem as CompatibleDigestItem>::sassafras_seal(signature);

		let mut import_block = BlockImportParams::new(BlockOrigin::Own, header);
		// import_block.post_digests.push(digest_item);
		// import_block.body = Some(body);
		// import_block.state_action =
		// 	StateAction::ApplyChanges(sc_consensus::StorageChanges::Changes(storage_changes));
		// import_block.intermediates.insert(
		// 	Cow::from(INTERMEDIATE_KEY),
		// 	Box::new(SassafrasIntermediate::<B> { epoch_descriptor }) as Box<_>,
		// );

		Ok(import_block)
	}

	fn force_authoring(&self) -> bool {
		// TODO-SASS
		//self.force_authoring
		false
	}

	fn should_backoff(&self, _slot: Slot, _chain_head: &B::Header) -> bool {
		// TODO-SASS
		// if let Some(ref strategy) = self.backoff_authoring_blocks {
		// 	if let Ok(chain_head_slot) =
		// 		find_pre_digest::<B>(chain_head).map(|digest| digest.slot())
		// 	{
		// 		return strategy.should_backoff(
		// 			*chain_head.number(),
		// 			chain_head_slot,
		// 			self.client.info().finalized_number,
		// 			slot,
		// 			self.logging_target(),
		// 		)
		// 	}
		// }
		// false
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
		//self.telemetry.clone()
		None
	}

	fn proposing_remaining_duration(&self, _slot_info: &SlotInfo<B>) -> Duration {
		// TODO-SASS
		// let parent_slot = find_pre_digest::<B>(&slot_info.chain_head).ok().map(|d| d.slot());
		//
		// sc_consensus_slots::proposing_remaining_duration(
		// 	parent_slot,
		// 	slot_info,
		// 	&self.block_proposal_slot_portion,
		// 	self.max_block_proposal_slot_portion.as_ref(),
		// 	sc_consensus_slots::SlotLenienceType::Exponential,
		// 	self.logging_target(),
		// )

		Duration::default()
	}
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
			"Verifying origin: {:?} header: {:?} justification(s): {:?} body: {:?}",
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

		debug!(target: "sassafras", "We have {:?} logs in this header", block.header.digest().logs().len());

		// TODO-SASS-SASS
		Ok((block, Default::default()))

		// TODO-SASS-SASS
		// let hash = block.header.hash();
		// let parent_hash = *block.header.parent_hash();

		// let create_inherent_data_providers = self
		// 	.create_inherent_data_providers
		// 	.create_inherent_data_providers(parent_hash, ())
		// 	.await
		// 	.map_err(|e| Error::<Block>::Client(sp_consensus::Error::from(e).into()))?;

		// let slot_now = create_inherent_data_providers.slot();

		// let parent_header_metadata = self
		// 	.client
		// 	.header_metadata(parent_hash)
		// 	.map_err(Error::<Block>::FetchParentHeader)?;

		// let pre_digest = find_pre_digest::<Block>(&block.header)?;
		// let (check_header, epoch_descriptor) = {
		// 	let epoch_changes = self.epoch_changes.shared_data();
		// 	let epoch_descriptor = epoch_changes
		// 		.epoch_descriptor_for_child_of(
		// 			descendent_query(&*self.client),
		// 			&parent_hash,
		// 			parent_header_metadata.number,
		// 			pre_digest.slot(),
		// 		)
		// 		.map_err(|e| Error::<Block>::ForkTree(Box::new(e)))?
		// 		.ok_or(Error::<Block>::FetchEpoch(parent_hash))?;
		// 	let viable_epoch = epoch_changes
		// 		.viable_epoch(&epoch_descriptor, |slot| {
		// 			Epoch::genesis(&self.config.genesis_config, slot)
		// 		})
		// 		.ok_or(Error::<Block>::FetchEpoch(parent_hash))?;

		// 	// We add one to the current slot to allow for some small drift.
		// 	// FIXME #1019 in the future, alter this queue to allow deferring of headers
		// 	let v_params = verification::VerificationParams {
		// 		header: block.header.clone(),
		// 		pre_digest: Some(pre_digest),
		// 		slot_now: slot_now + 1,
		// 		epoch: viable_epoch.as_ref(),
		// 	};

		// 	(verification::check_header::<Block>(v_params)?, epoch_descriptor)
		// };

		// match check_header {
		// 	CheckedHeader::Checked(pre_header, verified_info) => {
		// 		let sassafras_pre_digest = verified_info
		// 			.pre_digest
		// 			.as_sassafras_pre_digest()
		// 			.expect("check_header always returns a pre-digest digest item; qed");
		// 		let slot = sassafras_pre_digest.slot();

		// 		// the header is valid but let's check if there was something else already
		// 		// proposed at the same slot by the given author. if there was, we will
		// 		// report the equivocation to the runtime.
		// 		if let Err(err) = self
		// 			.check_and_report_equivocation(
		// 				slot_now,
		// 				slot,
		// 				&block.header,
		// 				&verified_info.author,
		// 				&block.origin,
		// 			)
		// 			.await
		// 		{
		// 			warn!(target: "sassafras", "Error checking/reporting BABE equivocation: {}", err);
		// 		}

		// 		// if the body is passed through, we need to use the runtime
		// 		// to check that the internally-set timestamp in the inherents
		// 		// actually matches the slot set in the seal.
		// 		if let Some(inner_body) = block.body {
		// 			let mut inherent_data = create_inherent_data_providers
		// 				.create_inherent_data()
		// 				.map_err(Error::<Block>::CreateInherents)?;
		// 			inherent_data.sassafras_replace_inherent_data(slot);
		// 			let new_block = Block::new(pre_header.clone(), inner_body);

		// 			self.check_inherents(
		// 				new_block.clone(),
		// 				BlockId::Hash(parent_hash),
		// 				inherent_data,
		// 				create_inherent_data_providers,
		// 				block.origin.into(),
		// 			)
		// 			.await?;

		// 			let (_, inner_body) = new_block.deconstruct();
		// 			block.body = Some(inner_body);
		// 		}

		// 		trace!(target: "sassafras", "Checked {:?}; importing.", pre_header);
		// 		telemetry!(
		// 			self.telemetry;
		// 			CONSENSUS_TRACE;
		// 			"sassafras.checked_and_importing";
		// 			"pre_header" => ?pre_header,
		// 		);

		// 		block.header = pre_header;
		// 		block.post_digests.push(verified_info.seal);
		// 		block.intermediates.insert(
		// 			Cow::from(INTERMEDIATE_KEY),
		// 			Box::new(SassafrasIntermediate::<Block> { epoch_descriptor }) as Box<_>,
		// 		);
		// 		block.post_hash = Some(hash);

		// 		Ok((block, Default::default()))
		// 	},
		// 	CheckedHeader::Deferred(a, b) => {
		// 		debug!(target: "sassafras", "Checking {:?} failed; {:?}, {:?}.", hash, a, b);
		// 		telemetry!(
		// 			self.telemetry;
		// 			CONSENSUS_DEBUG;
		// 			"sassafras.header_too_far_in_future";
		// 			"hash" => ?hash, "a" => ?a, "b" => ?b
		// 		);
		// 		Err(Error::<Block>::TooFarInFuture(hash).into())
		// 	},
		// }
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
		block: BlockImportParams<Block, Self::Transaction>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		let import_result = self.inner.import_block(block, new_cache).await;

		// revert to the original epoch changes in case there's an error
		// importing the block
		if import_result.is_err() {}

		import_result.map_err(Into::into)
	}

	async fn check_block(
		&mut self,
		block: BlockCheckParams<Block>,
	) -> Result<ImportResult, Self::Error> {
		self.inner.check_block(block).await.map_err(Into::into)
	}
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
	C: AuxStore
		// + HeaderBackend<Block>
		// + HeaderMetadata<Block, Error = sp_blockchain::Error>
		// + PreCommitActions<Block>
		+ 'static,
{
	let epoch_changes = aux_schema::load_epoch_changes::<B, _>(&*client)?;

	let link = SassafrasLink { epoch_changes: epoch_changes.clone(), config: config.clone() };

	// NOTE: this isn't entirely necessary, but since we didn't use to prune the
	// epoch tree it is useful as a migration, so that nodes prune long trees on
	// startup rather than waiting until importing the next epoch change block.
	//TODO-SASS
	//prune_finalized(client.clone(), &mut epoch_changes.shared_data())?;

	// TODO-SASS: Eventually register cleanup finality actions
	// let client_weak = Arc::downgrade(&client);
	// let on_finality = move |summary: &FinalityNotification<Block>| {
	// 	if let Some(client) = client_weak.upgrade() {
	// 		aux_storage_cleanup(client.as_ref(), summary)
	// 	} else {
	// 		Default::default()
	// 	}
	// };
	// client.register_finality_action(Box::new(on_finality));

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
