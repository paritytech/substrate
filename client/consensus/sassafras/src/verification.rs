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

//! Types and functions related to block verification.

use super::*;

// Allowed slot drift.
const MAX_SLOT_DRIFT: u64 = 1;

/// Verification parameters
struct VerificationParams<'a, B: 'a + BlockT> {
	/// The header being verified.
	header: B::Header,
	/// The pre-digest of the header being verified.
	pre_digest: &'a PreDigest,
	/// The slot number of the current time.
	slot_now: Slot,
	/// Epoch descriptor of the epoch this block _should_ be under, if it's valid.
	epoch: &'a Epoch,
	/// Expected ticket for this block.
	ticket: Option<Ticket>,
}

/// Verified information
struct VerifiedHeaderInfo {
	/// Authority index.
	authority_id: AuthorityId,
	/// Seal found within the header.
	seal: DigestItem,
}

/// Check a header has been signed by the right key. If the slot is too far in
/// the future, an error will be returned. If successful, returns the pre-header
/// and the digest item containing the seal.
///
/// The seal must be the last digest. Otherwise, the whole header is considered
/// unsigned. This is required for security and must not be changed.
///
/// The given header can either be from a primary or secondary slot assignment,
/// with each having different validation logic.
fn check_header<B: BlockT + Sized>(
	params: VerificationParams<B>,
) -> Result<CheckedHeader<B::Header, VerifiedHeaderInfo>, Error<B>> {
	let VerificationParams { mut header, pre_digest, slot_now, epoch, ticket } = params;
	let config = &epoch.config;

	// Check that the slot is not in the future, with some drift being allowed.
	if pre_digest.slot > slot_now + MAX_SLOT_DRIFT {
		return Ok(CheckedHeader::Deferred(header, pre_digest.slot))
	}

	let authority_id = match config.authorities.get(pre_digest.authority_idx as usize) {
		Some(authority_id) => authority_id.0.clone(),
		None => return Err(sassafras_err(Error::SlotAuthorNotFound)),
	};

	// Check header signature

	let seal = header
		.digest_mut()
		.pop()
		.ok_or_else(|| sassafras_err(Error::HeaderUnsealed(header.hash())))?;

	let signature = seal
		.as_sassafras_seal()
		.ok_or_else(|| sassafras_err(Error::HeaderBadSeal(header.hash())))?;

	let pre_hash = header.hash();
	if !AuthorityPair::verify(&signature, &pre_hash, &authority_id) {
		return Err(sassafras_err(Error::BadSignature(pre_hash)))
	}

	// Check authorship method and claim

	match (&ticket, &pre_digest.ticket_aux) {
		(Some(ticket), Some(ticket_aux)) => {
			log::debug!(target: "sassafras", "🌳 checking primary");
			let transcript =
				make_ticket_transcript(&config.randomness, ticket_aux.attempt, epoch.epoch_idx);
			schnorrkel::PublicKey::from_bytes(authority_id.as_slice())
				.and_then(|p| p.vrf_verify(transcript, &ticket.output, &ticket_aux.proof))
				.map_err(|s| sassafras_err(Error::VRFVerificationFailed(s)))?;
		},
		(None, None) => {
			log::debug!(target: "sassafras", "🌳 checking secondary");
			let idx = authorship::secondary_authority_index(pre_digest.slot, config);
			if idx != pre_digest.authority_idx {
				log::error!(target: "sassafras", "🌳 Bad secondary authority index");
				return Err(Error::SlotAuthorNotFound)
			}
		},
		(Some(_), None) => {
			log::warn!(target: "sassafras", "🌳 Unexpected secondary authoring mechanism");
			return Err(Error::UnexpectedAuthoringMechanism)
		},
		(None, Some(_)) => {
			log::warn!(target: "sassafras", "🌳 Unexpected primary authoring mechanism");
			return Err(Error::UnexpectedAuthoringMechanism)
		},
	}

	// Check slot-vrf proof

	let transcript = make_slot_transcript(&config.randomness, pre_digest.slot, epoch.epoch_idx);
	schnorrkel::PublicKey::from_bytes(authority_id.as_slice())
		.and_then(|p| p.vrf_verify(transcript, &pre_digest.vrf_output, &pre_digest.vrf_proof))
		.map_err(|s| sassafras_err(Error::VRFVerificationFailed(s)))?;

	let info = VerifiedHeaderInfo { authority_id, seal };

	Ok(CheckedHeader::Checked(header, info))
}

/// A verifier for Sassafras blocks.
pub struct SassafrasVerifier<Block: BlockT, Client, SelectChain, CIDP> {
	client: Arc<Client>,
	select_chain: SelectChain,
	create_inherent_data_providers: CIDP,
	epoch_changes: SharedEpochChanges<Block, Epoch>,
	telemetry: Option<TelemetryHandle>,
	genesis_config: SassafrasConfiguration,
}

impl<Block: BlockT, Client, SelectChain, CIDP> SassafrasVerifier<Block, Client, SelectChain, CIDP> {
	/// Constructor.
	pub fn new(
		client: Arc<Client>,
		select_chain: SelectChain,
		create_inherent_data_providers: CIDP,
		epoch_changes: SharedEpochChanges<Block, Epoch>,
		telemetry: Option<TelemetryHandle>,
		genesis_config: SassafrasConfiguration,
	) -> Self {
		SassafrasVerifier {
			client,
			select_chain,
			create_inherent_data_providers,
			epoch_changes,
			telemetry,
			genesis_config,
		}
	}
}

impl<Block, Client, SelectChain, CIDP> SassafrasVerifier<Block, Client, SelectChain, CIDP>
where
	Block: BlockT,
	Client: AuxStore + HeaderBackend<Block> + HeaderMetadata<Block> + ProvideRuntimeApi<Block>,
	Client::Api: BlockBuilderApi<Block> + SassafrasApi<Block>,
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
		// Don't report any equivocations during initial sync as they are most likely stale.
		if *origin == BlockOrigin::NetworkInitialSync {
			return Ok(())
		}

		// Check if authorship of this header is an equivocation and return a proof if so.
		let equivocation_proof = match sc_consensus_slots::check_equivocation(
			&*self.client,
			slot_now,
			slot,
			header,
			author,
		)
		.map_err(Error::Client)?
		{
			Some(proof) => proof,
			None => return Ok(()),
		};

		info!(
			target: "sassafras",
			"🌳 Slot author {:?} is equivocating at slot {} with headers {:?} and {:?}",
			author,
			slot,
			equivocation_proof.first_header.hash(),
			equivocation_proof.second_header.hash(),
		);

		// Get the best block on which we will build and send the equivocation report.
		let best_id = self
			.select_chain
			.best_chain()
			.await
			.map(|h| BlockId::Hash(h.hash()))
			.map_err(|e| Error::Client(e.into()))?;

		// Generate a key ownership proof. We start by trying to generate the key owernship proof
		// at the parent of the equivocating header, this will make sure that proof generation is
		// successful since it happens during the on-going session (i.e. session keys are available
		// in the state to be able to generate the proof). This might fail if the equivocation
		// happens on the first block of the session, in which case its parent would be on the
		// previous session. If generation on the parent header fails we try with best block as
		// well.
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

		info!(target: "sassafras", "🌳 Submitted equivocation report for author {:?}", author);

		Ok(())
	}
}

type BlockVerificationResult<Block> =
	Result<(BlockImportParams<Block, ()>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String>;

#[async_trait::async_trait]
impl<Block, Client, SelectChain, CIDP> Verifier<Block>
	for SassafrasVerifier<Block, Client, SelectChain, CIDP>
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
	CIDP: CreateInherentDataProviders<Block, ()> + Send + Sync,
	CIDP::InherentDataProviders: InherentDataProviderExt + Send + Sync,
{
	async fn verify(
		&mut self,
		mut import_params: BlockImportParams<Block, ()>,
	) -> BlockVerificationResult<Block> {
		trace!(
			target: "sassafras",
			"🌳 Verifying origin: {:?} header: {:?} justification(s): {:?} body: {:?}",
			import_params.origin,
			import_params.header,
			import_params.justifications,
			import_params.body,
		);

		if import_params.with_state() {
			// When importing whole state we don't calculate epoch descriptor, but rather
			// read it from the state after import. We also skip all verifications
			// because there's no parent state and we trust the sync module to verify
			// that the state is correct and finalized.
			return Ok((import_params, Default::default()))
		}

		let hash = import_params.header.hash();
		let parent_hash = *import_params.header.parent_hash();

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

		let pre_digest = find_pre_digest::<Block>(&import_params.header)?;

		let (checked_header, epoch_descriptor) = {
			let epoch_changes = self.epoch_changes.shared_data();
			let epoch_descriptor = epoch_changes
				.epoch_descriptor_for_child_of(
					descendent_query(&*self.client),
					&parent_hash,
					parent_header_metadata.number,
					pre_digest.slot,
				)
				.map_err(|e| Error::<Block>::ForkTree(Box::new(e)))?
				.ok_or(Error::<Block>::FetchEpoch(parent_hash))?;
			let viable_epoch = epoch_changes
				.viable_epoch(&epoch_descriptor, |slot| Epoch::genesis(&self.genesis_config, slot))
				.ok_or(Error::<Block>::FetchEpoch(parent_hash))?;

			let ticket = self
				.client
				.runtime_api()
				.slot_ticket(&BlockId::Hash(parent_hash), pre_digest.slot)
				.map_err(|err| err.to_string())?;

			let verification_params = VerificationParams {
				header: import_params.header.clone(),
				pre_digest: &pre_digest,
				slot_now,
				epoch: viable_epoch.as_ref(),
				ticket,
			};
			let checked_header = check_header::<Block>(verification_params)?;

			(checked_header, epoch_descriptor)
		};

		match checked_header {
			CheckedHeader::Checked(pre_header, verified_info) => {
				// The header is valid but let's check if there was something else already
				// proposed at the same slot by the given author. If there was, we will
				// report the equivocation to the runtime.
				if let Err(err) = self
					.check_and_report_equivocation(
						slot_now,
						pre_digest.slot,
						&import_params.header,
						&verified_info.authority_id,
						&import_params.origin,
					)
					.await
				{
					warn!(target: "sassafras", "🌳 Error checking/reporting Sassafras equivocation: {}", err);
				}

				// If the body is passed through, we need to use the runtime to check that the
				// internally-set timestamp in the inherents actually matches the slot set in the
				// seal.
				if let Some(inner_body) = import_params.body {
					let mut inherent_data = create_inherent_data_providers
						.create_inherent_data()
						.map_err(Error::<Block>::CreateInherents)?;
					inherent_data.sassafras_replace_inherent_data(pre_digest.slot);
					let block = Block::new(pre_header.clone(), inner_body);

					self.check_inherents(
						block.clone(),
						BlockId::Hash(parent_hash),
						inherent_data,
						create_inherent_data_providers,
						import_params.origin.into(),
					)
					.await?;

					let (_, inner_body) = block.deconstruct();
					import_params.body = Some(inner_body);
				}

				trace!(target: "sassafras", "🌳 Checked {:?}; importing.", pre_header);
				telemetry!(
					self.telemetry;
					CONSENSUS_TRACE;
					"sassafras.checked_and_importing";
					"pre_header" => ?pre_header,
				);

				import_params.header = pre_header;
				import_params.post_hash = Some(hash);
				import_params.post_digests.push(verified_info.seal);
				import_params.insert_intermediate(
					INTERMEDIATE_KEY,
					SassafrasIntermediate::<Block> { epoch_descriptor },
				);

				Ok((import_params, Default::default()))
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
