// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! rpc api for babe.

use crate::{Epoch, SharedEpochChanges, authorship, Config};
use futures::{FutureExt as _, TryFutureExt as _};
use jsonrpc_core::{
	Error as RpcError,
	futures::future as rpc_future,
};
use jsonrpc_derive::rpc;
use sc_consensus_epochs::{descendent_query, Epoch as EpochT};
use sp_consensus_babe::{
	AuthorityId,
	BabeApi as BabeRuntimeApi,
	digests::PreDigest,
};
use serde::{Deserialize, Serialize};
use sc_keystore::KeyStorePtr;
use sp_api::{ProvideRuntimeApi, BlockId};
use sp_core::crypto::Pair;
use sp_runtime::traits::{Block as BlockT, Header as _};
use sp_consensus::{SelectChain, Error as ConsensusError};
use sp_blockchain::{HeaderBackend, HeaderMetadata, Error as BlockChainError};
use std::{collections::HashMap, fmt, sync::Arc};

type FutureResult<T> = Box<dyn rpc_future::Future<Item = T, Error = RpcError> + Send>;

/// Provides rpc methods for interacting with Babe.
#[rpc]
pub trait BabeApi {
	/// Returns data about which slots (primary or secondary) can be claimed in the current epoch
	/// with the keys in the keystore.
	#[rpc(name = "babe_epochAuthorship")]
	fn epoch_authorship(&self) -> FutureResult<HashMap<AuthorityId, EpochAuthorship>>;
}

/// Implements the BabeRPC trait for interacting with Babe.
///
/// Uses a background thread to calculate epoch_authorship data.
pub struct BabeRPCHandler<B: BlockT, C, SC> {
	/// shared refernce to the client.
	client: Arc<C>,
	/// shared reference to EpochChanges
	shared_epoch_changes: SharedEpochChanges<B, Epoch>,
	/// shared reference to the Keystore
	keystore: KeyStorePtr,
	/// config (actually holds the slot duration)
	babe_config: Config,
	/// select chain
	select_chain: SC,
}

impl<B: BlockT, C, SC> BabeRPCHandler<B, C, SC> {
	/// creates a new instance of the BabeRpc handler.
	pub fn new(
		client: Arc<C>,
		shared_epoch_changes: SharedEpochChanges<B, Epoch>,
		keystore: KeyStorePtr,
		babe_config: Config,
		select_chain: SC,
	) -> Self {

		Self {
			client,
			shared_epoch_changes,
			keystore,
			babe_config,
			select_chain,
		}
	}
}

impl<B, C, SC> BabeApi for BabeRPCHandler<B, C, SC>
	where
		B: BlockT,
		C: ProvideRuntimeApi<B> + HeaderBackend<B> + HeaderMetadata<B, Error=BlockChainError> + 'static,
		C::Api: BabeRuntimeApi<B>,
		<C::Api as sp_api::ApiErrorExt>::Error: fmt::Debug,
		SC: SelectChain<B> + Clone + 'static,
{
	fn epoch_authorship(&self) -> FutureResult<HashMap<AuthorityId, EpochAuthorship>> {
		let (
			babe_config,
			keystore,
			shared_epoch,
			client,
			select_chain,
		) = (
			self.babe_config.clone(),
			self.keystore.clone(),
			self.shared_epoch_changes.clone(),
			self.client.clone(),
			self.select_chain.clone(),
		);
		let future = async move {
			let header = select_chain.best_chain().map_err(Error::Consensus)?;
			let epoch_start = client.runtime_api()
				.current_epoch_start(&BlockId::Hash(header.hash()))
				.map_err(|err| {
					Error::StringError(format!("{:?}", err))
				})?;
			let epoch = epoch_data(&shared_epoch, &client, &babe_config, epoch_start, &select_chain)?;
			let (epoch_start, epoch_end) = (epoch.start_slot(), epoch.end_slot());

			let mut claims: HashMap<AuthorityId, EpochAuthorship> = HashMap::new();

			for slot_number in epoch_start..epoch_end {
				let epoch = epoch_data(&shared_epoch, &client, &babe_config, slot_number, &select_chain)?;
				if let Some((claim, key)) = authorship::claim_slot(slot_number, &epoch, &babe_config, &keystore) {
					match claim {
						PreDigest::Primary { .. } => {
							claims.entry(key.public()).or_default().primary.push(slot_number);
						}
						PreDigest::Secondary { .. } => {
							claims.entry(key.public()).or_default().secondary.push(slot_number);
						}
					};
				}
			}

			Ok(claims)
		}.boxed();

		Box::new(future.compat())
	}
}

/// Holds information about the `slot_number`'s that can be claimed by a given key.
#[derive(Default, Debug, Deserialize, Serialize)]
pub struct EpochAuthorship {
	/// the array of primary slots that can be claimed
	primary: Vec<u64>,
	/// the array of secondary slots that can be claimed
	secondary: Vec<u64>,
}

/// Errors encountered by the RPC
#[derive(Debug, derive_more::Display, derive_more::From)]
pub enum Error {
	/// Consensus error
	Consensus(ConsensusError),
	/// Errors that can be formatted as a String
	StringError(String)
}

impl From<Error> for jsonrpc_core::Error {
	fn from(error: Error) -> Self {
		jsonrpc_core::Error {
			message: format!("{}", error).into(),
			code: jsonrpc_core::ErrorCode::ServerError(1234),
			data: None,
		}
	}
}

/// fetches the epoch data for a given slot_number.
fn epoch_data<B, C, SC>(
	epoch_changes: &SharedEpochChanges<B, Epoch>,
	client: &Arc<C>,
	babe_config: &Config,
	slot_number: u64,
	select_chain: &SC,
) -> Result<Epoch, Error>
	where
		B: BlockT,
		C: HeaderBackend<B> + HeaderMetadata<B, Error=BlockChainError> + 'static,
		SC: SelectChain<B>,
{
	let parent = select_chain.best_chain()?;
	epoch_changes.lock().epoch_for_child_of(
		descendent_query(&**client),
		&parent.hash(),
		parent.number().clone(),
		slot_number,
		|slot| babe_config.genesis_epoch(slot),
	)
		.map_err(|e| Error::Consensus(ConsensusError::ChainLookup(format!("{:?}", e))))?
		.map(|e| e.into_inner())
		.ok_or(Error::Consensus(ConsensusError::InvalidAuthoritiesSet))
}
