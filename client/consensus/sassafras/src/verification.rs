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
use crate::inherents::SassafrasInherentData;
use sp_core::{
	crypto::{VrfPublic, Wraps},
	ed25519::Pair as EphemeralPair,
};

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
	/// Origin
	origin: BlockOrigin,
	/// Expected ticket for this block.
	maybe_ticket: Option<(TicketId, TicketBody)>,
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
	let VerificationParams { mut header, pre_digest, slot_now, epoch, origin, maybe_ticket } =
		params;

	let seal = header
		.digest_mut()
		.pop()
		.ok_or_else(|| sassafras_err(Error::HeaderUnsealed(header.hash())))?;

	// Check that the slot is not in the future, with some drift being allowed.
	if pre_digest.slot > slot_now + MAX_SLOT_DRIFT {
		header.digest_mut().push(seal);
		return Ok(CheckedHeader::Deferred(header, pre_digest.slot))
	}

	let Some(authority_id) = epoch.authorities.get(pre_digest.authority_idx as usize) else {
		return Err(sassafras_err(Error::SlotAuthorNotFound))
	};

	// Check header signature (aka the Seal)

	let signature = seal
		.as_sassafras_seal()
		.ok_or_else(|| sassafras_err(Error::HeaderBadSeal(header.hash())))?;

	let pre_hash = header.hash();
	if !AuthorityPair::verify(&signature, &pre_hash, authority_id) {
		return Err(sassafras_err(Error::BadSignature(pre_hash)))
	}

	// Optionally check ticket ownership

	let mut sign_data =
		vrf::slot_claim_sign_data(&epoch.randomness, pre_digest.slot, epoch.epoch_idx);

	match (&maybe_ticket, &pre_digest.ticket_claim) {
		(Some((_ticket_id, ticket_body)), ticket_claim) => {
			debug!(target: LOG_TARGET, "checking primary");

			sign_data.push_transcript_data(&ticket_body.encode());

			// Revealed key check
			let revealed_input = vrf::revealed_key_input(
				&epoch.randomness,
				ticket_body.attempt_idx,
				epoch.epoch_idx,
			);
			let revealed_output = pre_digest
				.vrf_signature
				.outputs
				.get(1)
				.ok_or_else(|| sassafras_err(Error::MissingSignedVrfOutput))?;
			let revealed_seed = vrf::make_revealed_key_seed(&revealed_input, &revealed_output);
			let revealed_public = EphemeralPair::from_seed(&revealed_seed).public();
			if revealed_public != ticket_body.revealed_public {
				return Err(sassafras_err(Error::RevealPublicMismatch))
			}
			sign_data.push_vrf_input(revealed_input).expect("Can't fail; qed");

			if let Some(ticket_claim) = ticket_claim {
				// Optional check, increases some score...
				let challenge = sign_data.challenge::<32>();
				if !EphemeralPair::verify(
					&ticket_claim.erased_signature,
					&challenge,
					&ticket_body.erased_public,
				) {
					return Err(sassafras_err(Error::BadSignature(pre_hash)))
				}
			}
		},
		(None, None) => {
			debug!(target: LOG_TARGET, "checking secondary");
			let idx = authorship::secondary_authority_index(pre_digest.slot, epoch);
			if idx != pre_digest.authority_idx {
				error!(target: LOG_TARGET, "Bad secondary authority index");
				return Err(Error::SlotAuthorNotFound)
			}
		},
		(None, Some(_)) =>
			if origin != BlockOrigin::NetworkInitialSync {
				warn!(target: LOG_TARGET, "Unexpected primary authoring mechanism");
				return Err(Error::UnexpectedAuthoringMechanism)
			},
	}

	// Check per-slot vrf proof
	if !authority_id.as_inner_ref().vrf_verify(&sign_data, &pre_digest.vrf_signature) {
		warn!(target: LOG_TARGET, ">>> VERIFICATION FAILED (pri = {})!!!", maybe_ticket.is_some());
		return Err(sassafras_err(Error::VrfVerificationFailed))
	}
	warn!(target: LOG_TARGET, ">>> VERIFICATION OK (pri = {})!!!", maybe_ticket.is_some());

	let info = VerifiedHeaderInfo { authority_id: authority_id.clone(), seal };

	Ok(CheckedHeader::Checked(header, info))
}

/// A verifier for Sassafras blocks.
pub struct SassafrasVerifier<Block: BlockT, Client, SelectChain, CIDP> {
	client: Arc<Client>,
	select_chain: SelectChain,
	create_inherent_data_providers: CIDP,
	epoch_changes: SharedEpochChanges<Block, Epoch>,
	genesis_config: Epoch,
	telemetry: Option<TelemetryHandle>,
}

impl<Block: BlockT, Client, SelectChain, CIDP> SassafrasVerifier<Block, Client, SelectChain, CIDP> {
	/// Constructor.
	pub fn new(
		client: Arc<Client>,
		select_chain: SelectChain,
		create_inherent_data_providers: CIDP,
		epoch_changes: SharedEpochChanges<Block, Epoch>,
		genesis_config: Epoch,
		telemetry: Option<TelemetryHandle>,
	) -> Self {
		SassafrasVerifier {
			client,
			select_chain,
			create_inherent_data_providers,
			epoch_changes,
			genesis_config,
			telemetry,
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
		at_hash: Block::Hash,
		inherent_data: InherentData,
		create_inherent_data_providers: CIDP::InherentDataProviders,
	) -> Result<(), Error<Block>> {
		let inherent_res = self
			.client
			.runtime_api()
			.check_inherents(at_hash, block, inherent_data)
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
			target: LOG_TARGET,
			"🌳 Slot author {:?} is equivocating at slot {} with headers {:?} and {:?}",
			author,
			slot,
			equivocation_proof.first_header.hash(),
			equivocation_proof.second_header.hash(),
		);

		// Get the best block on which we will build and send the equivocation report.
		let best_hash = self
			.select_chain
			.best_chain()
			.await
			.map(|h| h.hash())
			.map_err(|e| Error::Client(e.into()))?;

		// Generate a key ownership proof. We start by trying to generate the key owernship proof
		// at the parent of the equivocating header, this will make sure that proof generation is
		// successful since it happens during the on-going session (i.e. session keys are available
		// in the state to be able to generate the proof). This might fail if the equivocation
		// happens on the first block of the session, in which case its parent would be on the
		// previous session. If generation on the parent header fails we try with best block as
		// well.
		let generate_key_owner_proof = |at_hash: Block::Hash| {
			self.client
				.runtime_api()
				.generate_key_ownership_proof(at_hash, slot, equivocation_proof.offender.clone())
				.map_err(Error::RuntimeApi)
		};

		let parent_hash = *header.parent_hash();
		let key_owner_proof = match generate_key_owner_proof(parent_hash)? {
			Some(proof) => proof,
			None => match generate_key_owner_proof(best_hash)? {
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
				best_hash,
				equivocation_proof,
				key_owner_proof,
			)
			.map_err(Error::RuntimeApi)?;

		info!(target: LOG_TARGET, "Submitted equivocation report for author {:?}", author);

		Ok(())
	}
}

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
		mut block: BlockImportParams<Block, ()>,
	) -> Result<BlockImportParams<Block, ()>, String> {
		trace!(
			target: LOG_TARGET,
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
			// Just insert a tag to notify that this is indeed a Sassafras block to the
			// `BlockImport` implementation.
			block.insert_intermediate(INTERMEDIATE_KEY, ());
			return Ok(block)
		}

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

			let maybe_ticket = self
				.client
				.runtime_api()
				.slot_ticket(parent_hash, pre_digest.slot)
				.ok()
				.unwrap_or_else(|| None);

			let verification_params = VerificationParams {
				header: block.header.clone(),
				pre_digest: &pre_digest,
				slot_now,
				epoch: viable_epoch.as_ref(),
				origin: block.origin,
				maybe_ticket,
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
						&block.header,
						&verified_info.authority_id,
						&block.origin,
					)
					.await
				{
					warn!(
						target: LOG_TARGET,
						"Error checking/reporting equivocation: {}", err
					);
				}

				// If the body is passed through, we need to use the runtime to check that the
				// internally-set timestamp in the inherents actually matches the slot set in the
				// seal.
				if let Some(inner_body) = block.body {
					let new_block = Block::new(pre_header.clone(), inner_body);

					if !block.state_action.skip_execution_checks() {
						// TODO-SASS-P3 : @davxy??? DOC
						let mut inherent_data = create_inherent_data_providers
							.create_inherent_data()
							.await
							.map_err(Error::<Block>::CreateInherents)?;
						inherent_data.sassafras_replace_inherent_data(&pre_digest.slot);
						self.check_inherents(
							new_block.clone(),
							parent_hash,
							inherent_data,
							create_inherent_data_providers,
						)
						.await?;
					}

					let (_, inner_body) = new_block.deconstruct();
					block.body = Some(inner_body);
				}

				trace!(target: LOG_TARGET, "Checked {:?}; importing.", pre_header);
				telemetry!(
					self.telemetry;
					CONSENSUS_TRACE;
					"sassafras.checked_and_importing";
					"pre_header" => ?pre_header,
				);

				block.header = pre_header;
				block.post_hash = Some(hash);
				// TODO DAVXY: seal required???
				block.post_digests.push(verified_info.seal);
				block.insert_intermediate(
					INTERMEDIATE_KEY,
					SassafrasIntermediate::<Block> { epoch_descriptor },
				);

				Ok(block)
			},
			CheckedHeader::Deferred(a, b) => {
				debug!(target: LOG_TARGET, "Checking {:?} failed; {:?}, {:?}.", hash, a, b);
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
