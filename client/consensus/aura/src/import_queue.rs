// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
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

//! Module implementing the logic for verifying and importing AuRa blocks.

use crate::{
	aura_err, authorities, find_pre_digest, slot_author, AuthorityId, CompatibilityMode, Error,
	LOG_TARGET,
};
use codec::{Codec, Decode, Encode};
use log::{debug, info, trace};
use prometheus_endpoint::Registry;
use sc_client_api::{backend::AuxStore, BlockOf, UsageProvider};
use sc_consensus::{
	block_import::{BlockImport, BlockImportParams, ForkChoiceStrategy},
	import_queue::{BasicQueue, BoxJustificationImport, DefaultImportQueue, Verifier},
};
use sc_consensus_slots::{check_equivocation, CheckedHeader, InherentDataProviderExt};
use sc_telemetry::{telemetry, TelemetryHandle, CONSENSUS_DEBUG, CONSENSUS_TRACE};
use sp_api::{ApiExt, ProvideRuntimeApi};
use sp_block_builder::BlockBuilder as BlockBuilderApi;
use sp_blockchain::{well_known_cache_keys::Id as CacheKeyId, HeaderBackend};
use sp_consensus::Error as ConsensusError;
use sp_consensus_aura::{digests::CompatibleDigestItem, inherents::AuraInherentData, AuraApi};
use sp_consensus_slots::Slot;
use sp_core::{crypto::Pair, ExecutionContext};
use sp_inherents::{CreateInherentDataProviders, InherentDataProvider as _};
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header, NumberFor},
	DigestItem,
};
use std::{fmt::Debug, hash::Hash, marker::PhantomData, sync::Arc};

/// check a header has been signed by the right key. If the slot is too far in the future, an error
/// will be returned. If it's successful, returns the pre-header and the digest item
/// containing the seal.
///
/// This digest item will always return `Some` when used with `as_aura_seal`.
fn check_header<C, B: BlockT, P: Pair>(
	client: &C,
	slot_now: Slot,
	mut header: B::Header,
	hash: B::Hash,
	authorities: &[AuthorityId<P>],
	check_for_equivocation: CheckForEquivocation,
) -> Result<CheckedHeader<B::Header, (Slot, DigestItem)>, Error<B>>
where
	P::Signature: Codec,
	C: sc_client_api::backend::AuxStore,
	P::Public: Encode + Decode + PartialEq + Clone,
{
	let seal = header.digest_mut().pop().ok_or(Error::HeaderUnsealed(hash))?;

	let sig = seal.as_aura_seal().ok_or_else(|| aura_err(Error::HeaderBadSeal(hash)))?;

	let slot = find_pre_digest::<B, P::Signature>(&header)?;

	if slot > slot_now {
		header.digest_mut().push(seal);
		Ok(CheckedHeader::Deferred(header, slot))
	} else {
		// check the signature is valid under the expected authority and
		// chain state.
		let expected_author =
			slot_author::<P>(slot, authorities).ok_or(Error::SlotAuthorNotFound)?;

		let pre_hash = header.hash();

		if P::verify(&sig, pre_hash.as_ref(), expected_author) {
			if check_for_equivocation.check_for_equivocation() {
				if let Some(equivocation_proof) =
					check_equivocation(client, slot_now, slot, &header, expected_author)
						.map_err(Error::Client)?
				{
					info!(
						target: LOG_TARGET,
						"Slot author is equivocating at slot {} with headers {:?} and {:?}",
						slot,
						equivocation_proof.first_header.hash(),
						equivocation_proof.second_header.hash(),
					);
				}
			}

			Ok(CheckedHeader::Checked(header, (slot, seal)))
		} else {
			Err(Error::BadSignature(hash))
		}
	}
}

/// A verifier for Aura blocks.
pub struct AuraVerifier<C, P, CIDP, N> {
	client: Arc<C>,
	phantom: PhantomData<P>,
	create_inherent_data_providers: CIDP,
	check_for_equivocation: CheckForEquivocation,
	telemetry: Option<TelemetryHandle>,
	compatibility_mode: CompatibilityMode<N>,
}

impl<C, P, CIDP, N> AuraVerifier<C, P, CIDP, N> {
	pub(crate) fn new(
		client: Arc<C>,
		create_inherent_data_providers: CIDP,
		check_for_equivocation: CheckForEquivocation,
		telemetry: Option<TelemetryHandle>,
		compatibility_mode: CompatibilityMode<N>,
	) -> Self {
		Self {
			client,
			create_inherent_data_providers,
			check_for_equivocation,
			telemetry,
			compatibility_mode,
			phantom: PhantomData,
		}
	}
}

impl<C, P, CIDP, N> AuraVerifier<C, P, CIDP, N>
where
	P: Send + Sync + 'static,
	CIDP: Send,
{
	async fn check_inherents<B: BlockT>(
		&self,
		block: B,
		block_id: BlockId<B>,
		inherent_data: sp_inherents::InherentData,
		create_inherent_data_providers: CIDP::InherentDataProviders,
		execution_context: ExecutionContext,
	) -> Result<(), Error<B>>
	where
		C: ProvideRuntimeApi<B>,
		C::Api: BlockBuilderApi<B>,
		CIDP: CreateInherentDataProviders<B, ()>,
	{
		let inherent_res = self
			.client
			.runtime_api()
			.check_inherents_with_context(&block_id, execution_context, block, inherent_data)
			.map_err(|e| Error::Client(e.into()))?;

		if !inherent_res.ok() {
			for (i, e) in inherent_res.into_errors() {
				match create_inherent_data_providers.try_handle_error(&i, &e).await {
					Some(res) => res.map_err(Error::Inherent)?,
					None => return Err(Error::UnknownInherentError(i)),
				}
			}
		}

		Ok(())
	}
}

#[async_trait::async_trait]
impl<B: BlockT, C, P, CIDP> Verifier<B> for AuraVerifier<C, P, CIDP, NumberFor<B>>
where
	C: ProvideRuntimeApi<B> + Send + Sync + sc_client_api::backend::AuxStore,
	C::Api: BlockBuilderApi<B> + AuraApi<B, AuthorityId<P>> + ApiExt<B>,
	P: Pair + Send + Sync + 'static,
	P::Public: Send + Sync + Hash + Eq + Clone + Decode + Encode + Debug + 'static,
	P::Signature: Encode + Decode,
	CIDP: CreateInherentDataProviders<B, ()> + Send + Sync,
	CIDP::InherentDataProviders: InherentDataProviderExt + Send + Sync,
{
	async fn verify(
		&mut self,
		mut block: BlockImportParams<B, ()>,
	) -> Result<(BlockImportParams<B, ()>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
		if block.with_state() {
			// When importing whole state we don't verify the seal as the state is not available.
			return Ok((block, Default::default()))
		}

		let hash = block.header.hash();
		let parent_hash = *block.header.parent_hash();
		let authorities = authorities(
			self.client.as_ref(),
			parent_hash,
			*block.header.number(),
			&self.compatibility_mode,
		)
		.map_err(|e| format!("Could not fetch authorities at {:?}: {}", parent_hash, e))?;

		let create_inherent_data_providers = self
			.create_inherent_data_providers
			.create_inherent_data_providers(parent_hash, ())
			.await
			.map_err(|e| Error::<B>::Client(sp_blockchain::Error::Application(e)))?;

		let mut inherent_data = create_inherent_data_providers
			.create_inherent_data()
			.await
			.map_err(Error::<B>::Inherent)?;

		let slot_now = create_inherent_data_providers.slot();

		// we add one to allow for some small drift.
		// FIXME #1019 in the future, alter this queue to allow deferring of
		// headers
		let checked_header = check_header::<C, B, P>(
			&self.client,
			slot_now + 1,
			block.header,
			hash,
			&authorities[..],
			self.check_for_equivocation,
		)
		.map_err(|e| e.to_string())?;
		match checked_header {
			CheckedHeader::Checked(pre_header, (slot, seal)) => {
				// if the body is passed through, we need to use the runtime
				// to check that the internally-set timestamp in the inherents
				// actually matches the slot set in the seal.
				if let Some(inner_body) = block.body.take() {
					let new_block = B::new(pre_header.clone(), inner_body);

					inherent_data.aura_replace_inherent_data(slot);

					// skip the inherents verification if the runtime API is old or not expected to
					// exist.
					if !block.state_action.skip_execution_checks() &&
						self.client
							.runtime_api()
							.has_api_with::<dyn BlockBuilderApi<B>, _>(
								&BlockId::Hash(parent_hash),
								|v| v >= 2,
							)
							.map_err(|e| e.to_string())?
					{
						self.check_inherents(
							new_block.clone(),
							BlockId::Hash(parent_hash),
							inherent_data,
							create_inherent_data_providers,
							block.origin.into(),
						)
						.await
						.map_err(|e| e.to_string())?;
					}

					let (_, inner_body) = new_block.deconstruct();
					block.body = Some(inner_body);
				}

				trace!(target: LOG_TARGET, "Checked {:?}; importing.", pre_header);
				telemetry!(
					self.telemetry;
					CONSENSUS_TRACE;
					"aura.checked_and_importing";
					"pre_header" => ?pre_header,
				);

				block.header = pre_header;
				block.post_digests.push(seal);
				block.fork_choice = Some(ForkChoiceStrategy::LongestChain);
				block.post_hash = Some(hash);

				Ok((block, None))
			},
			CheckedHeader::Deferred(a, b) => {
				debug!(target: LOG_TARGET, "Checking {:?} failed; {:?}, {:?}.", hash, a, b);
				telemetry!(
					self.telemetry;
					CONSENSUS_DEBUG;
					"aura.header_too_far_in_future";
					"hash" => ?hash,
					"a" => ?a,
					"b" => ?b,
				);
				Err(format!("Header {:?} rejected: too far in the future", hash))
			},
		}
	}
}

/// Should we check for equivocation of a block author?
#[derive(Debug, Clone, Copy)]
pub enum CheckForEquivocation {
	/// Yes, check for equivocation.
	///
	/// This is the default setting for this.
	Yes,
	/// No, don't check for equivocation.
	No,
}

impl CheckForEquivocation {
	/// Should we check for equivocation?
	fn check_for_equivocation(self) -> bool {
		matches!(self, Self::Yes)
	}
}

impl Default for CheckForEquivocation {
	fn default() -> Self {
		Self::Yes
	}
}

/// Parameters of [`import_queue`].
pub struct ImportQueueParams<'a, Block: BlockT, I, C, S, CIDP> {
	/// The block import to use.
	pub block_import: I,
	/// The justification import.
	pub justification_import: Option<BoxJustificationImport<Block>>,
	/// The client to interact with the chain.
	pub client: Arc<C>,
	/// Something that can create the inherent data providers.
	pub create_inherent_data_providers: CIDP,
	/// The spawner to spawn background tasks.
	pub spawner: &'a S,
	/// The prometheus registry.
	pub registry: Option<&'a Registry>,
	/// Should we check for equivocation?
	pub check_for_equivocation: CheckForEquivocation,
	/// Telemetry instance used to report telemetry metrics.
	pub telemetry: Option<TelemetryHandle>,
	/// Compatibility mode that should be used.
	///
	/// If in doubt, use `Default::default()`.
	pub compatibility_mode: CompatibilityMode<NumberFor<Block>>,
}

/// Start an import queue for the Aura consensus algorithm.
pub fn import_queue<P, Block, I, C, S, CIDP>(
	ImportQueueParams {
		block_import,
		justification_import,
		client,
		create_inherent_data_providers,
		spawner,
		registry,
		check_for_equivocation,
		telemetry,
		compatibility_mode,
	}: ImportQueueParams<Block, I, C, S, CIDP>,
) -> Result<DefaultImportQueue<Block, C>, sp_consensus::Error>
where
	Block: BlockT,
	C::Api: BlockBuilderApi<Block> + AuraApi<Block, AuthorityId<P>> + ApiExt<Block>,
	C: 'static
		+ ProvideRuntimeApi<Block>
		+ BlockOf
		+ Send
		+ Sync
		+ AuxStore
		+ UsageProvider<Block>
		+ HeaderBackend<Block>,
	I: BlockImport<Block, Error = ConsensusError, Transaction = sp_api::TransactionFor<C, Block>>
		+ Send
		+ Sync
		+ 'static,
	P: Pair + Send + Sync + 'static,
	P::Public: Clone + Eq + Send + Sync + Hash + Debug + Encode + Decode,
	P::Signature: Encode + Decode,
	S: sp_core::traits::SpawnEssentialNamed,
	CIDP: CreateInherentDataProviders<Block, ()> + Sync + Send + 'static,
	CIDP::InherentDataProviders: InherentDataProviderExt + Send + Sync,
{
	let verifier = build_verifier::<P, _, _, _>(BuildVerifierParams {
		client,
		create_inherent_data_providers,
		check_for_equivocation,
		telemetry,
		compatibility_mode,
	});

	Ok(BasicQueue::new(verifier, Box::new(block_import), justification_import, spawner, registry))
}

/// Parameters of [`build_verifier`].
pub struct BuildVerifierParams<C, CIDP, N> {
	/// The client to interact with the chain.
	pub client: Arc<C>,
	/// Something that can create the inherent data providers.
	pub create_inherent_data_providers: CIDP,
	/// Should we check for equivocation?
	pub check_for_equivocation: CheckForEquivocation,
	/// Telemetry instance used to report telemetry metrics.
	pub telemetry: Option<TelemetryHandle>,
	/// Compatibility mode that should be used.
	///
	/// If in doubt, use `Default::default()`.
	pub compatibility_mode: CompatibilityMode<N>,
}

/// Build the [`AuraVerifier`]
pub fn build_verifier<P, C, CIDP, N>(
	BuildVerifierParams {
		client,
		create_inherent_data_providers,
		check_for_equivocation,
		telemetry,
		compatibility_mode,
	}: BuildVerifierParams<C, CIDP, N>,
) -> AuraVerifier<C, P, CIDP, N> {
	AuraVerifier::<_, P, _, _>::new(
		client,
		create_inherent_data_providers,
		check_for_equivocation,
		telemetry,
		compatibility_mode,
	)
}
