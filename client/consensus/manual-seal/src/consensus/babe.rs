// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

//! BABE consensus data provider, This allows manual seal author blocks that are valid for runtimes
//! that expect babe-specific digests.

use super::ConsensusDataProvider;
use crate::Error;
use codec::Encode;
use sc_client_api::{AuxStore, UsageProvider};
use sc_consensus_babe::{
	authorship, find_pre_digest, BabeIntermediate, CompatibleDigestItem, Config, Session,
	INTERMEDIATE_KEY,
};
use sc_consensus_sessions::{
	descendent_query, SessionHeader, SharedSessionChanges, ViableSessionDescriptor,
};
use sp_keystore::SyncCryptoStorePtr;
use std::{borrow::Cow, sync::Arc};

use sc_consensus::{BlockImportParams, ForkChoiceStrategy, Verifier};
use sp_api::{ProvideRuntimeApi, TransactionFor};
use sp_blockchain::{HeaderBackend, HeaderMetadata};
use sp_consensus::CacheKeyId;
use sp_consensus_babe::{
	digests::{NextSessionDescriptor, PreDigest, SecondaryPlainPreDigest},
	inherents::BabeInherentData,
	AuthorityId, BabeApi, BabeAuthorityWeight, ConsensusLog, BABE_ENGINE_ID,
};
use sp_consensus_slots::Slot;
use sp_inherents::InherentData;
use sp_runtime::{
	generic::{BlockId, Digest},
	traits::{Block as BlockT, Header},
	DigestItem,
};
use sp_timestamp::TimestampInherentData;

/// Provides BABE-compatible predigests and BlockImportParams.
/// Intended for use with BABE runtimes.
pub struct BabeConsensusDataProvider<B: BlockT, C> {
	/// shared reference to keystore
	keystore: SyncCryptoStorePtr,

	/// Shared reference to the client.
	client: Arc<C>,

	/// Shared session changes
	session_changes: SharedSessionChanges<B, Session>,

	/// BABE config, gotten from the runtime.
	config: Config,

	/// Authorities to be used for this babe chain.
	authorities: Vec<(AuthorityId, BabeAuthorityWeight)>,
}

/// Verifier to be used for babe chains
pub struct BabeVerifier<B: BlockT, C> {
	/// Shared session changes
	session_changes: SharedSessionChanges<B, Session>,

	/// Shared reference to the client.
	client: Arc<C>,
}

impl<B: BlockT, C> BabeVerifier<B, C> {
	/// create a nrew verifier
	pub fn new(session_changes: SharedSessionChanges<B, Session>, client: Arc<C>) -> BabeVerifier<B, C> {
		BabeVerifier { session_changes, client }
	}
}

/// The verifier for the manual seal engine; instantly finalizes.
#[async_trait::async_trait]
impl<B, C> Verifier<B> for BabeVerifier<B, C>
where
	B: BlockT,
	C: HeaderBackend<B> + HeaderMetadata<B, Error = sp_blockchain::Error>,
{
	async fn verify(
		&mut self,
		mut import_params: BlockImportParams<B, ()>,
	) -> Result<(BlockImportParams<B, ()>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
		import_params.finalized = false;
		import_params.fork_choice = Some(ForkChoiceStrategy::LongestChain);

		let pre_digest = find_pre_digest::<B>(&import_params.header)?;

		let parent_hash = import_params.header.parent_hash();
		let parent = self
			.client
			.header(BlockId::Hash(*parent_hash))
			.ok()
			.flatten()
			.ok_or_else(|| format!("header for block {} not found", parent_hash))?;
		let session_changes = self.session_changes.shared_data();
		let session_descriptor = session_changes
			.session_descriptor_for_child_of(
				descendent_query(&*self.client),
				&parent.hash(),
				parent.number().clone(),
				pre_digest.slot(),
			)
			.map_err(|e| format!("failed to fetch session_descriptor: {}", e))?
			.ok_or_else(|| format!("{}", sp_consensus::Error::InvalidAuthoritiesSet))?;
		// drop the lock
		drop(session_changes);

		import_params.intermediates.insert(
			Cow::from(INTERMEDIATE_KEY),
			Box::new(BabeIntermediate::<B> { session_descriptor }) as Box<_>,
		);

		Ok((import_params, None))
	}
}

impl<B, C> BabeConsensusDataProvider<B, C>
where
	B: BlockT,
	C: AuxStore
		+ HeaderBackend<B>
		+ ProvideRuntimeApi<B>
		+ HeaderMetadata<B, Error = sp_blockchain::Error>
		+ UsageProvider<B>,
	C::Api: BabeApi<B>,
{
	pub fn new(
		client: Arc<C>,
		keystore: SyncCryptoStorePtr,
		session_changes: SharedSessionChanges<B, Session>,
		authorities: Vec<(AuthorityId, BabeAuthorityWeight)>,
	) -> Result<Self, Error> {
		if authorities.is_empty() {
			return Err(Error::StringError("Cannot supply empty authority set!".into()))
		}

		let config = Config::get(&*client)?;

		Ok(Self { config, client, keystore, session_changes, authorities })
	}

	fn session(&self, parent: &B::Header, slot: Slot) -> Result<Session, Error> {
		let session_changes = self.session_changes.shared_data();
		let session_descriptor = session_changes
			.session_descriptor_for_child_of(
				descendent_query(&*self.client),
				&parent.hash(),
				parent.number().clone(),
				slot,
			)
			.map_err(|e| Error::StringError(format!("failed to fetch session_descriptor: {}", e)))?
			.ok_or_else(|| sp_consensus::Error::InvalidAuthoritiesSet)?;

		let session = session_changes
			.viable_session(&session_descriptor, |slot| {
				Session::genesis(self.config.genesis_config(), slot)
			})
			.ok_or_else(|| {
				log::info!(target: "babe", "create_digest: no viable_session :(");
				sp_consensus::Error::InvalidAuthoritiesSet
			})?;

		Ok(session.as_ref().clone())
	}
}

impl<B, C> ConsensusDataProvider<B> for BabeConsensusDataProvider<B, C>
where
	B: BlockT,
	C: AuxStore
		+ HeaderBackend<B>
		+ HeaderMetadata<B, Error = sp_blockchain::Error>
		+ UsageProvider<B>
		+ ProvideRuntimeApi<B>,
	C::Api: BabeApi<B>,
{
	type Transaction = TransactionFor<C, B>;

	fn create_digest(&self, parent: &B::Header, inherents: &InherentData) -> Result<Digest, Error> {
		let slot = inherents
			.babe_inherent_data()?
			.ok_or_else(|| Error::StringError("No babe inherent data".into()))?;
		let session = self.session(parent, slot)?;

		// this is a dev node environment, we should always be able to claim a slot.
		let logs = if let Some((predigest, _)) =
			authorship::claim_slot(slot, &session, &self.keystore)
		{
			vec![<DigestItem as CompatibleDigestItem>::babe_pre_digest(predigest)]
		} else {
			// well we couldn't claim a slot because this is an existing chain and we're not in the
			// authorities. we need to tell BabeBlockImport that the session has changed, and we put
			// ourselves in the authorities.
			let predigest =
				PreDigest::SecondaryPlain(SecondaryPlainPreDigest { slot, authority_index: 0_u32 });

			let mut session_changes = self.session_changes.shared_data();
			let session_descriptor = session_changes
				.session_descriptor_for_child_of(
					descendent_query(&*self.client),
					&parent.hash(),
					parent.number().clone(),
					slot,
				)
				.map_err(|e| {
					Error::StringError(format!("failed to fetch session_descriptor: {}", e))
				})?
				.ok_or_else(|| sp_consensus::Error::InvalidAuthoritiesSet)?;

			match session_descriptor {
				ViableSessionDescriptor::Signaled(identifier, _session_header) => {
					let session_mut = session_changes
						.session_mut(&identifier)
						.ok_or_else(|| sp_consensus::Error::InvalidAuthoritiesSet)?;

					// mutate the current session
					session_mut.authorities = self.authorities.clone();

					let next_session = ConsensusLog::NextSessionData(NextSessionDescriptor {
						authorities: self.authorities.clone(),
						// copy the old randomness
						randomness: session_mut.randomness.clone(),
					});

					vec![
						DigestItem::PreRuntime(BABE_ENGINE_ID, predigest.encode()),
						DigestItem::Consensus(BABE_ENGINE_ID, next_session.encode()),
					]
				},
				ViableSessionDescriptor::UnimportedGenesis(_) => {
					// since this is the genesis, secondary predigest works for now.
					vec![DigestItem::PreRuntime(BABE_ENGINE_ID, predigest.encode())]
				},
			}
		};

		Ok(Digest { logs })
	}

	fn append_block_import(
		&self,
		parent: &B::Header,
		params: &mut BlockImportParams<B, Self::Transaction>,
		inherents: &InherentData,
	) -> Result<(), Error> {
		let slot = inherents
			.babe_inherent_data()?
			.ok_or_else(|| Error::StringError("No babe inherent data".into()))?;
		let session_changes = self.session_changes.shared_data();
		let mut session_descriptor = session_changes
			.session_descriptor_for_child_of(
				descendent_query(&*self.client),
				&parent.hash(),
				parent.number().clone(),
				slot,
			)
			.map_err(|e| Error::StringError(format!("failed to fetch session_descriptor: {}", e)))?
			.ok_or_else(|| sp_consensus::Error::InvalidAuthoritiesSet)?;
		// drop the lock
		drop(session_changes);
		// a quick check to see if we're in the authorities
		let session = self.session(parent, slot)?;
		let (authority, _) = self.authorities.first().expect("authorities is non-emptyp; qed");
		let has_authority = session.authorities.iter().any(|(id, _)| *id == *authority);

		if !has_authority {
			log::info!(target: "manual-seal", "authority not found");
			let timestamp = inherents
				.timestamp_inherent_data()?
				.ok_or_else(|| Error::StringError("No timestamp inherent data".into()))?;

			let slot = Slot::from_timestamp(timestamp, self.config.slot_duration());

			// manually hard code session descriptor
			session_descriptor = match session_descriptor {
				ViableSessionDescriptor::Signaled(identifier, _header) =>
					ViableSessionDescriptor::Signaled(
						identifier,
						SessionHeader {
							start_slot: slot,
							end_slot: (*slot * self.config.genesis_config().session_length).into(),
						},
					),
				_ => unreachable!(
					"we're not in the authorities, so this isn't the genesis session; qed"
				),
			};
		}

		params.intermediates.insert(
			Cow::from(INTERMEDIATE_KEY),
			Box::new(BabeIntermediate::<B> { session_descriptor }) as Box<_>,
		);

		Ok(())
	}
}
