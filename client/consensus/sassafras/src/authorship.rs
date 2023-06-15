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

//! Types and functions related to authority selection and slot claiming.

use super::*;

use sp_consensus_sassafras::{
	digests::PreDigest, slot_claim_sign_data, ticket_id, ticket_id_threshold, AuthorityId, Slot,
	TicketClaim, TicketData, TicketEnvelope, TicketId,
};
use sp_core::{bandersnatch::ring_vrf::RingVrfContext, ed25519, twox_64, ByteArray};
use std::pin::Pin;

/// Get secondary authority index for the given epoch and slot.
pub(crate) fn secondary_authority_index(
	slot: Slot,
	config: &SassafrasConfiguration,
) -> AuthorityIndex {
	u64::from_le_bytes((config.randomness, slot).using_encoded(twox_64)) as AuthorityIndex %
		config.authorities.len() as AuthorityIndex
}

/// Try to claim an epoch slot.
/// If ticket is `None`, then the slot should be claimed using the fallback mechanism.
pub(crate) fn claim_slot(
	slot: Slot,
	epoch: &mut Epoch,
	maybe_ticket: Option<(TicketId, TicketData)>,
	keystore: &KeystorePtr,
) -> Option<(PreDigest, AuthorityId)> {
	let config = &epoch.config;

	if config.authorities.is_empty() {
		return None
	}

	let mut vrf_sign_data = slot_claim_sign_data(&config.randomness, slot, epoch.epoch_idx);

	let (authority_idx, ticket_claim) = match maybe_ticket {
		Some((ticket_id, ticket_data)) => {
			log::debug!(target: LOG_TARGET, "[TRY PRIMARY (slot {slot}, tkt = {ticket_id:16x})]");
			let (authority_idx, ticket_secret) = epoch.tickets_aux.remove(&ticket_id)?.clone();
			log::debug!(
				target: LOG_TARGET,
				"   got ticket: auth: {}, attempt: {}",
				authority_idx,
				ticket_data.attempt_idx
			);

			vrf_sign_data.push_transcript_data(&ticket_data.encode());

			let data = vrf_sign_data.challenge::<32>();
			let erased_pair = ed25519::Pair::from_seed(&ticket_secret.erased_secret);
			let erased_signature = *erased_pair.sign(&data).as_ref();

			let claim = TicketClaim { erased_signature };
			(authority_idx, Some(claim))
		},
		None => {
			log::debug!(target: LOG_TARGET, "[TRY SECONDARY (slot {slot})]");
			(secondary_authority_index(slot, config), None)
		},
	};

	let authority_id = config.authorities.get(authority_idx as usize)?;

	let vrf_signature = keystore
		.bandersnatch_vrf_sign(AuthorityId::ID, authority_id.as_ref(), &vrf_sign_data)
		.ok()
		.flatten()?;

	let pre_digest = PreDigest { authority_idx, slot, vrf_signature, ticket_claim };

	Some((pre_digest, authority_id.clone()))
}

/// Generate the tickets for the given epoch.
///
/// Tickets additional information will be stored within the `Epoch` structure.
/// The additional information will be used later during the epoch to claim slots.
fn generate_epoch_tickets(
	epoch: &mut Epoch,
	keystore: &KeystorePtr,
	ring_ctx: &RingVrfContext,
) -> Vec<TicketEnvelope> {
	let config = &epoch.config;
	let max_attempts = config.threshold_params.attempts_number;
	let redundancy_factor = config.threshold_params.redundancy_factor;
	let mut tickets = Vec::new();

	let threshold = ticket_id_threshold(
		redundancy_factor,
		config.epoch_duration as u32,
		max_attempts,
		config.authorities.len() as u32,
	);
	// TODO-SASS-P4 remove me
	log::debug!(target: LOG_TARGET, "Generating tickets for epoch {} @ slot {}", epoch.epoch_idx, epoch.start_slot);
	log::debug!(target: LOG_TARGET, "    threshold: {threshold:016x}");

	// We need a list of raw unwrapped keys
	let pks: Vec<_> = config.authorities.iter().map(|a| *a.as_ref()).collect();

	for (authority_idx, authority_id) in config.authorities.iter().enumerate() {
		if !keystore.has_keys(&[(authority_id.to_raw_vec(), AuthorityId::ID)]) {
			continue
		}

		debug!(target: LOG_TARGET, ">>> Generating new ring prover key...");
		let prover = ring_ctx.prover(&pks, authority_idx).unwrap();
		debug!(target: LOG_TARGET, ">>> ...done");

		let make_ticket = |attempt_idx| {
			let vrf_input = ticket_id_vrf_input(&config.randomness, attempt_idx, epoch.epoch_idx);

			let vrf_preout = keystore
				.bandersnatch_vrf_output(AuthorityId::ID, authority_id.as_ref(), &vrf_input)
				.ok()??;

			let ticket_id = ticket_id(&vrf_input, &vrf_preout);
			if ticket_id >= threshold {
				return None
			}

			let (erased_pair, erased_seed) = ed25519::Pair::generate();

			let erased_public: [u8; 32] = *erased_pair.public().as_ref();
			let revealed_public = [0; 32];
			let data = TicketData { attempt_idx, erased_public, revealed_public };

			debug!(target: LOG_TARGET, ">>> Creating ring proof for attempt {}", attempt_idx);
			let mut sign_data = ticket_body_sign_data(&data);
			sign_data.push_vrf_input(vrf_input).expect("Can't fail");

			let ring_signature = keystore
				.bandersnatch_ring_vrf_sign(
					AuthorityId::ID,
					authority_id.as_ref(),
					&sign_data,
					&prover,
				)
				.ok()??;
			debug!(target: LOG_TARGET, ">>> ...done");

			let ticket_envelope = TicketEnvelope { data, vrf_preout, ring_signature };

			let ticket_secret = TicketSecret { attempt_idx, erased_secret: erased_seed };

			Some((ticket_id, ticket_envelope, ticket_secret))
		};

		for attempt in 0..max_attempts {
			if let Some((ticket_id, ticket_envelope, ticket_secret)) = make_ticket(attempt) {
				log::debug!(target: LOG_TARGET, "    → {ticket_id:016x}");
				epoch
					.tickets_aux
					.insert(ticket_id, (authority_idx as AuthorityIndex, ticket_secret));
				tickets.push(ticket_envelope);
			}
		}
	}
	tickets
}

struct SlotWorker<B: BlockT, C, E, I, SO, L> {
	client: Arc<C>,
	block_import: I,
	env: E,
	sync_oracle: SO,
	justification_sync_link: L,
	force_authoring: bool,
	keystore: KeystorePtr,
	epoch_changes: SharedEpochChanges<B, Epoch>,
	slot_notification_sinks: SlotNotificationSinks<B>,
	genesis_config: SassafrasConfiguration,
}

#[async_trait::async_trait]
impl<B, C, E, I, ER, SO, L> sc_consensus_slots::SimpleSlotWorker<B>
	for SlotWorker<B, C, E, I, SO, L>
where
	B: BlockT,
	C: ProvideRuntimeApi<B> + HeaderBackend<B> + HeaderMetadata<B, Error = ClientError>,
	C::Api: SassafrasApi<B>,
	E: Environment<B, Error = ER> + Sync,
	E::Proposer: Proposer<B, Error = ER, Transaction = sp_api::TransactionFor<C, B>>,
	I: BlockImport<B, Transaction = sp_api::TransactionFor<C, B>> + Send + Sync + 'static,
	SO: SyncOracle + Send + Clone + Sync,
	L: sc_consensus::JustificationSyncLink<B>,
	ER: std::error::Error + Send + 'static,
{
	type Claim = (PreDigest, AuthorityId);
	type SyncOracle = SO;
	type JustificationSyncLink = L;
	type CreateProposer =
		Pin<Box<dyn Future<Output = Result<E::Proposer, ConsensusError>> + Send + 'static>>;
	type Proposer = E::Proposer;
	type BlockImport = I;
	type AuxData = ViableEpochDescriptor<B::Hash, NumberFor<B>, Epoch>;

	fn logging_target(&self) -> &'static str {
		LOG_TARGET
	}

	fn block_import(&mut self) -> &mut Self::BlockImport {
		&mut self.block_import
	}

	fn aux_data(&self, parent: &B::Header, slot: Slot) -> Result<Self::AuxData, ConsensusError> {
		self.epoch_changes
			.shared_data()
			.epoch_descriptor_for_child_of(
				descendent_query(&*self.client),
				&parent.hash(),
				*parent.number(),
				slot,
			)
			.map_err(|e| ConsensusError::ChainLookup(e.to_string()))?
			.ok_or(ConsensusError::InvalidAuthoritiesSet)
	}

	fn authorities_len(&self, epoch_descriptor: &Self::AuxData) -> Option<usize> {
		self.epoch_changes
			.shared_data()
			.viable_epoch(epoch_descriptor, |slot| Epoch::genesis(&self.genesis_config, slot))
			.map(|epoch| epoch.as_ref().config.authorities.len())
	}

	async fn claim_slot(
		&self,
		parent_header: &B::Header,
		slot: Slot,
		epoch_descriptor: &ViableEpochDescriptor<B::Hash, NumberFor<B>, Epoch>,
	) -> Option<Self::Claim> {
		// Get the next slot ticket from the runtime.
		let maybe_ticket =
			self.client.runtime_api().slot_ticket(parent_header.hash(), slot).ok()?;

		let mut epoch_changes = self.epoch_changes.shared_data_locked();
		let mut epoch = epoch_changes.viable_epoch_mut(epoch_descriptor, |slot| {
			Epoch::genesis(&self.genesis_config, slot)
		})?;

		let claim = authorship::claim_slot(slot, &mut epoch.as_mut(), maybe_ticket, &self.keystore);
		if claim.is_some() {
			debug!(target: LOG_TARGET, "Claimed slot {}", slot);
		}
		claim
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
					warn!(target: LOG_TARGET, "Trying to notify a slot but the channel is full");
					true
				} else {
					false
				},
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
		epoch_descriptor: Self::AuxData,
	) -> Result<
		sc_consensus::BlockImportParams<B, <Self::BlockImport as BlockImport<B>>::Transaction>,
		ConsensusError,
	> {
		// TODO DAVXY SASS-32: this seal may be revisited.
		// We already have a VRF signature, this could be completelly redundant.
		// The header.hash() can be added to the VRF signed data.
		// OR maybe we can maintain this seal but compute it using some of the data in the
		// pre-digest
		// Another option is to not recompute this signature and push (reuse) the one in the
		// pre-digest as the seal
		let signature = self
			.keystore
			.sign_with(
				<AuthorityId as AppCrypto>::ID,
				<AuthorityId as AppCrypto>::CRYPTO_ID,
				public.as_ref(),
				header_hash.as_ref(),
			)
			.map_err(|e| ConsensusError::CannotSign(format!("{}. Key {:?}", e, public)))?
			.ok_or_else(|| {
				ConsensusError::CannotSign(format!(
					"Could not find key in keystore. Key {:?}",
					public
				))
			})?;
		let signature: AuthoritySignature = signature
			.clone()
			.try_into()
			.map_err(|_| ConsensusError::InvalidSignature(signature, public.to_raw_vec()))?;

		let digest_item = <DigestItem as CompatibleDigestItem>::sassafras_seal(signature);

		let mut block = BlockImportParams::new(BlockOrigin::Own, header);
		block.post_digests.push(digest_item);
		block.body = Some(body);
		block.state_action =
			StateAction::ApplyChanges(sc_consensus::StorageChanges::Changes(storage_changes));
		block
			.insert_intermediate(INTERMEDIATE_KEY, SassafrasIntermediate::<B> { epoch_descriptor });

		Ok(block)
	}

	fn force_authoring(&self) -> bool {
		self.force_authoring
	}

	fn should_backoff(&self, _slot: Slot, _chain_head: &B::Header) -> bool {
		// TODO-SASS-P3
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
				.map_err(|e| ConsensusError::ClientImport(format!("{:?}", e))),
		)
	}

	fn telemetry(&self) -> Option<TelemetryHandle> {
		// TODO-SASS-P4
		None
	}

	fn proposing_remaining_duration(&self, slot_info: &SlotInfo<B>) -> Duration {
		let parent_slot = find_pre_digest::<B>(&slot_info.chain_head).ok().map(|d| d.slot);

		// TODO-SASS-P2 : clarify this field. In Sassafras this is part of 'self'
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

/// Authoring tickets generation worker.
///
/// Listens on the client's import notification stream for blocks which contains new epoch
/// information, that is blocks that signals the begin of a new epoch.
/// This event here triggers the begin of the generation of tickets for the next epoch.
/// The tickets generated by the worker are saved within the epoch changes tree
/// and are volatile.
async fn start_tickets_worker<B, C, SC>(
	client: Arc<C>,
	keystore: KeystorePtr,
	epoch_changes: SharedEpochChanges<B, Epoch>,
	select_chain: SC,
) where
	B: BlockT,
	C: BlockchainEvents<B> + ProvideRuntimeApi<B>,
	C::Api: SassafrasApi<B>,
	SC: SelectChain<B> + 'static,
{
	let mut notifications = client.import_notification_stream();

	while let Some(notification) = notifications.next().await {
		let epoch_desc = match find_next_epoch_digest::<B>(&notification.header) {
			Ok(Some(epoch_desc)) => epoch_desc,
			Err(err) => {
				warn!(target: LOG_TARGET, "Error fetching next epoch digest: {}", err);
				continue
			},
			_ => continue,
		};

		debug!(target: LOG_TARGET, "New epoch announced {:x?}", epoch_desc);

		let number = *notification.header.number();
		let position = if number == One::one() {
			EpochIdentifierPosition::Genesis1
		} else {
			EpochIdentifierPosition::Regular
		};
		let epoch_identifier = EpochIdentifier { position, hash: notification.hash, number };

		let mut epoch = match epoch_changes.shared_data().epoch(&epoch_identifier).cloned() {
			Some(epoch) => epoch,
			None => {
				warn!(
					target: LOG_TARGET,
					"Unexpected missing epoch data for {:?}", epoch_identifier
				);
				continue
			},
		};

		// Get the best block on which we will publish the tickets.
		let best_hash = match select_chain.best_chain().await {
			Ok(header) => header.hash(),
			Err(err) => {
				error!(target: LOG_TARGET, "Error fetching best chain block id: {}", err);
				continue
			},
		};

		let ring_ctx = match client.runtime_api().ring_context(best_hash) {
			Ok(Some(ctx)) => ctx,
			Ok(None) => {
				info!(target: LOG_TARGET, "Ring context not initialized yet");
				continue
			},
			Err(err) => {
				error!(target: LOG_TARGET, "Unable to read ring context: {}", err);
				continue
			},
		};

		let tickets = generate_epoch_tickets(&mut epoch, &keystore, &ring_ctx);
		if tickets.is_empty() {
			continue
		}

		let err = match client.runtime_api().submit_tickets_unsigned_extrinsic(best_hash, tickets) {
			Err(err) => Some(err.to_string()),
			Ok(false) => Some("Unknown reason".to_string()),
			_ => None,
		};

		match err {
			None => {
				// Cache tickets in the epoch changes tree
				epoch_changes
					.shared_data()
					.epoch_mut(&epoch_identifier)
					.map(|target_epoch| target_epoch.tickets_aux = epoch.tickets_aux);
				// TODO-SASS-P4: currently we don't persist the tickets proofs
				// Thus on reboot/crash we are loosing them.
			},
			Some(err) => {
				error!(target: LOG_TARGET, "Unable to submit tickets: {}", err);
			},
		}
	}
}

/// Worker for Sassafras which implements `Future<Output=()>`. This must be polled.
pub struct SassafrasWorker<B: BlockT> {
	inner: Pin<Box<dyn Future<Output = ()> + Send + 'static>>,
	slot_notification_sinks: SlotNotificationSinks<B>,
}

impl<B: BlockT> SassafrasWorker<B> {
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

/// Parameters for Sassafras.
pub struct SassafrasWorkerParams<B: BlockT, C, SC, EN, I, SO, L, CIDP> {
	/// The client to use
	pub client: Arc<C>,
	/// The keystore that manages the keys of the node.
	pub keystore: KeystorePtr,
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
	/// Force authoring of blocks even if we are offline.
	pub force_authoring: bool,
	/// State shared between import queue and authoring worker.
	pub sassafras_link: SassafrasLink<B>,
}

/// Start the Sassafras worker.
pub fn start_sassafras<B, C, SC, EN, I, SO, CIDP, L, ER>(
	SassafrasWorkerParams {
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
	}: SassafrasWorkerParams<B, C, SC, EN, I, SO, L, CIDP>,
) -> Result<SassafrasWorker<B>, ConsensusError>
where
	B: BlockT,
	C: ProvideRuntimeApi<B>
		+ ProvideUncles<B>
		+ BlockchainEvents<B>
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
	ER: std::error::Error + Send + From<ConsensusError> + From<I::Error> + 'static,
{
	info!(target: LOG_TARGET, "🍁 Starting Sassafras Authorship worker");

	let slot_notification_sinks = Arc::new(Mutex::new(Vec::new()));

	let slot_worker = SlotWorker {
		client: client.clone(),
		block_import,
		env,
		sync_oracle: sync_oracle.clone(),
		justification_sync_link,
		force_authoring,
		keystore: keystore.clone(),
		epoch_changes: sassafras_link.epoch_changes.clone(),
		slot_notification_sinks: slot_notification_sinks.clone(),
		genesis_config: sassafras_link.genesis_config.clone(),
	};

	let slot_worker = sc_consensus_slots::start_slot_worker(
		sassafras_link.genesis_config.slot_duration(),
		select_chain.clone(),
		sc_consensus_slots::SimpleSlotWorkerToSlotWorker(slot_worker),
		sync_oracle,
		create_inherent_data_providers,
	);

	let tickets_worker = start_tickets_worker(
		client.clone(),
		keystore,
		sassafras_link.epoch_changes.clone(),
		select_chain,
	);

	let inner = future::select(Box::pin(slot_worker), Box::pin(tickets_worker));

	Ok(SassafrasWorker { inner: Box::pin(inner.map(|_| ())), slot_notification_sinks })
}
