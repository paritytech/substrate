// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! BABE consensus data provider

use super::ConsensusDataProvider;
use crate::Error;
use codec::Encode;
use std::{
	any::Any,
	borrow::Cow,
	sync::{Arc, atomic},
	time::SystemTime,
};
use sc_client_api::AuxStore;
use sc_consensus_babe::{
	Config, Epoch, authorship, CompatibleDigestItem, BabeIntermediate,
	register_babe_inherent_data_provider, INTERMEDIATE_KEY, find_pre_digest,
};
use sc_consensus_epochs::{SharedEpochChanges, descendent_query, ViableEpochDescriptor, EpochIdentifier, EpochIdentifierPosition, EpochHeader};
use sc_keystore::KeyStorePtr;

use sp_api::{ProvideRuntimeApi, TransactionFor};
use sp_blockchain::{HeaderBackend, HeaderMetadata};
use sp_consensus::BlockImportParams;
use sp_consensus_babe::{
	BabeApi, inherents::BabeInherentData, ConsensusLog, BABE_ENGINE_ID, AuthorityId,
	digests::{PreDigest, SecondaryPlainPreDigest, NextEpochDescriptor},
};
use sp_inherents::{InherentDataProviders, InherentData, ProvideInherentData, InherentIdentifier};
use sp_runtime::{
	traits::{DigestItemFor, DigestFor, Block as BlockT},
	generic::Digest,
};
use sp_timestamp::{InherentType, InherentError, INHERENT_IDENTIFIER, TimestampInherentData};
use sp_keyring::Sr25519Keyring::Alice;
use sp_runtime::generic::BlockId;
use sp_runtime::traits::{Zero, Header};

/// Provides BABE-compatible predigests and BlockImportParams.
/// Intended for use with BABE runtimes.
pub struct BabeConsensusDataProvider<B: BlockT, C> {
	/// shared reference to keystore
	keystore: KeyStorePtr,

	/// Shared reference to the client.
	client: Arc<C>,

	/// Shared epoch changes
	epoch_changes: SharedEpochChanges<B, Epoch>,

	/// BABE config, gotten from the runtime.
	config: Config,
}

impl<B, C> BabeConsensusDataProvider<B, C>
	where
		B: BlockT,
		C: AuxStore + HeaderBackend<B> + ProvideRuntimeApi<B>,
		C::Api: BabeApi<B, Error = sp_blockchain::Error>,
{
	pub fn new(
		client: Arc<C>,
		keystore: KeyStorePtr,
		provider: &InherentDataProviders,
		epoch_changes: SharedEpochChanges<B, Epoch>,
	) -> Result<Self, Error> {
		let config = Config::get_or_compute(&*client)?;
		let timestamp_provider = SlotTimestampProvider::new(client.clone())?;

		provider.register_provider(timestamp_provider)?;
		register_babe_inherent_data_provider(provider, config.slot_duration)?;

		Ok(Self {
			config,
			client,
			keystore,
			epoch_changes,
		})
	}
}

impl<B, C> ConsensusDataProvider<B> for BabeConsensusDataProvider<B, C>
	where
		B: BlockT,
		C: AuxStore + HeaderBackend<B> + HeaderMetadata<B, Error = sp_blockchain::Error> + ProvideRuntimeApi<B>,
		C::Api: BabeApi<B, Error = sp_blockchain::Error>,
{
	type Transaction = TransactionFor<C, B>;

	fn create_digest(&self, parent: &B::Header, inherents: &InherentData) -> Result<DigestFor<B>, Error> {
		let slot_number = inherents.babe_inherent_data()?;

		let epoch_changes = self.epoch_changes.lock();
		let epoch_descriptor = epoch_changes
			.epoch_descriptor_for_child_of(
				descendent_query(&*self.client),
				&parent.hash(),
				parent.number().clone(),
				slot_number,
			)
			.map_err(|e| Error::StringError(format!("failed to fetch epoch_descriptor: {}", e)))?
			.ok_or_else(|| sp_consensus::Error::InvalidAuthoritiesSet)?;

		let epoch = epoch_changes
			.viable_epoch(
				&epoch_descriptor,
				|slot| Epoch::genesis(&self.config, slot),
			)
			.ok_or_else(|| {
				log::info!(target: "babe", "create_digest: no viable_epoch :(");
				sp_consensus::Error::InvalidAuthoritiesSet
			})?;

		// this is a dev node environment, we should always be able to claim a slot.
		let logs =  if let Some((predigest, _)) = authorship::claim_slot(slot_number, epoch.as_ref(), &self.keystore) {
			vec![
				<DigestItemFor<B> as CompatibleDigestItem>::babe_pre_digest(predigest),
			]
		} else {
			// well we couldn't claim a slot because this is an existing chain and we're not in the authorities.
			// we need to tell BabeBlockImport that the epoch has changed, and we put ourselves in the authorities.
			let predigest = PreDigest::SecondaryPlain(SecondaryPlainPreDigest {
				slot_number,
				authority_index: 0_u32,
			});

			let authority = (AuthorityId::from(Alice.public()), 0);

			let next_epoch = ConsensusLog::NextEpochData(NextEpochDescriptor {
				authorities: vec![authority],
				// copy the old randomness
				randomness: epoch.as_ref().randomness.clone()
			});

			vec![
				DigestItemFor::<B>::PreRuntime(BABE_ENGINE_ID, predigest.encode()),
				DigestItemFor::<B>::Consensus(BABE_ENGINE_ID, next_epoch.encode())
			]
		};

		Ok(Digest { logs })
	}

	fn append_block_import(
		&self,
		parent: &B::Header,
		params: &mut BlockImportParams<B, Self::Transaction>,
		inherents: &InherentData
	) -> Result<(), Error> {
		let slot_number = inherents.babe_inherent_data()?;
		let epoch_changes = self.epoch_changes.lock();

		let mut epoch_descriptor = epoch_changes
			.epoch_descriptor_for_child_of(
				descendent_query(&*self.client),
				&parent.hash(),
				parent.number().clone(),
				slot_number,
			)
			.map_err(|e| Error::StringError(format!("failed to fetch epoch data: {}", e)))?
			.ok_or_else(|| sp_consensus::Error::InvalidAuthoritiesSet)?;

		let epoch = epoch_changes
			.viable_epoch(
				&epoch_descriptor,
				|slot| Epoch::genesis(&self.config, slot),
			)
			.ok_or_else(|| {
				log::info!(target: "babe", "create_digest: no viable_epoch :(");
				sp_consensus::Error::InvalidAuthoritiesSet
			})?;

		// a quick check to see if we're in the authorities
		let has_authority = epoch.as_ref()
			.authorities
			.iter()
			.find(|(id, _)| {
				*id == AuthorityId::from(Alice.public())
			})
			.is_some();

		if !has_authority {
			log::info!(target: "babe", "authority not found");
			let slot_number = inherents.timestamp_inherent_data()? / self.config.slot_duration;
			// manually hard code epoch descriptor
			epoch_descriptor = ViableEpochDescriptor::Signaled(
				EpochIdentifier {
					position: EpochIdentifierPosition::Regular,
					hash: parent.hash(),
					number: parent.number().clone()
				},
				EpochHeader {
					start_slot: slot_number,
					end_slot: slot_number + self.config.epoch_length,
				}
			);
		}

		params.intermediates.insert(
			Cow::from(INTERMEDIATE_KEY),
			Box::new(BabeIntermediate::<B> { epoch_descriptor }) as Box<dyn Any>,
		);

		Ok(())
	}
}

/// Provide duration since unix epoch in millisecond for timestamp inherent.
/// Mocks the timestamp inherent to always produce the timestamp for the next babe slot.
struct SlotTimestampProvider {
	time: atomic::AtomicU64,
	slot_duration: u64
}

impl SlotTimestampProvider {
	/// create a new mocked time stamp provider.
	fn new<B, C>(client: Arc<C>) -> Result<Self, Error>
		where
			B: BlockT,
			C: AuxStore + HeaderBackend<B> + ProvideRuntimeApi<B>,
			C::Api: BabeApi<B, Error = sp_blockchain::Error>,
	{
		let slot_duration = Config::get_or_compute(&*client)?.slot_duration;
		let info = client.info();

		// looks like this isn't the first block, rehydrate the fake time.
		// otherwise we'd be producing blocks for older slots.
		let duration = if info.best_number != Zero::zero() {
			let header = client.header(BlockId::Hash(info.best_hash))?.unwrap();
			let slot_number = find_pre_digest::<B>(&header).unwrap().slot_number();
			// add the slot duration so there's no collision of slots
			(slot_number * slot_duration) + slot_duration
		} else {
			// this is the first block, use the correct time.
			let now = SystemTime::now();
			now.duration_since(SystemTime::UNIX_EPOCH)
				.map_err(|err| Error::StringError(format!("{}", err)))?
				.as_millis() as u64
		};

		Ok(Self {
			time: atomic::AtomicU64::new(duration),
			slot_duration,
		})
	}
}

impl ProvideInherentData for SlotTimestampProvider {
	fn inherent_identifier(&self) -> &'static InherentIdentifier {
		&INHERENT_IDENTIFIER
	}

	fn provide_inherent_data(&self, inherent_data: &mut InherentData) -> Result<(), sp_inherents::Error> {
		// we update the time here.
		let duration: InherentType = self.time.fetch_add(self.slot_duration, atomic::Ordering::SeqCst);
		inherent_data.put_data(INHERENT_IDENTIFIER, &duration)?;
		Ok(())
	}

	fn error_to_string(&self, error: &[u8]) -> Option<String> {
		InherentError::try_from(&INHERENT_IDENTIFIER, error).map(|e| format!("{:?}", e))
	}
}