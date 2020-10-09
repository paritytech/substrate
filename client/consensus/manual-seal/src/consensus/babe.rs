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

use std::{
	any::Any,
	borrow::Cow,
	sync::{Arc, atomic},
	time::SystemTime,
};
use sc_client_api::AuxStore;
use sc_consensus_babe::{
	Config, Epoch, authorship, CompatibleDigestItem, BabeIntermediate,
	register_babe_inherent_data_provider, INTERMEDIATE_KEY,
};
use sc_consensus_epochs::{SharedEpochChanges, descendent_query};

use sp_api::{ProvideRuntimeApi, TransactionFor};
use sp_blockchain::{HeaderBackend, HeaderMetadata};
use sp_consensus::BlockImportParams;
use sp_consensus_babe::{BabeApi, inherents::BabeInherentData};
use sp_keystore::SyncCryptoStorePtr;
use sp_inherents::{InherentDataProviders, InherentData, ProvideInherentData, InherentIdentifier};
use sp_runtime::{
	traits::{DigestItemFor, DigestFor, Block as BlockT, Header as _},
	generic::Digest,
};
use sp_timestamp::{InherentType, InherentError, INHERENT_IDENTIFIER};

/// Provides BABE-compatible predigests and BlockImportParams.
/// Intended for use with BABE runtimes.
pub struct BabeConsensusDataProvider<B: BlockT, C> {
	/// shared reference to keystore
	keystore: SyncCryptoStorePtr,

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
		C: AuxStore + ProvideRuntimeApi<B>,
		C::Api: BabeApi<B, Error = sp_blockchain::Error>,
{
	pub fn new(
		client: Arc<C>,
		keystore: SyncCryptoStorePtr,
		provider: &InherentDataProviders,
		epoch_changes: SharedEpochChanges<B, Epoch>,
	) -> Result<Self, Error> {
		let config = Config::get_or_compute(&*client)?;
		let timestamp_provider = SlotTimestampProvider::new(config.slot_duration)?;

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
		let (predigest, _) = authorship::claim_slot(slot_number, epoch.as_ref(), &self.keystore)
			.ok_or_else(|| Error::StringError("failed to claim slot for authorship".into()))?;

		Ok(Digest {
			logs: vec![
				<DigestItemFor<B> as CompatibleDigestItem>::babe_pre_digest(predigest),
			],
		})
	}

	fn append_block_import(
		&self,
		parent: &B::Header,
		params: &mut BlockImportParams<B, Self::Transaction>,
		inherents: &InherentData
	) -> Result<(), Error> {
		let slot_number = inherents.babe_inherent_data()?;

		let epoch_descriptor = self.epoch_changes.lock()
			.epoch_descriptor_for_child_of(
				descendent_query(&*self.client),
				&parent.hash(),
				parent.number().clone(),
				slot_number,
			)
			.map_err(|e| Error::StringError(format!("failed to fetch epoch data: {}", e)))?
			.ok_or_else(|| sp_consensus::Error::InvalidAuthoritiesSet)?;

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
	fn new(slot_duration: u64) -> Result<Self, Error> {
		let now = SystemTime::now();
		let duration = now.duration_since(SystemTime::UNIX_EPOCH)
			.map_err(|err| Error::StringError(format!("{}", err)))?;
		Ok(Self {
			time: atomic::AtomicU64::new(duration.as_millis() as u64),
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
