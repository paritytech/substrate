// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Combines [sc_rpc_api::state::StateApiClient] with [frame_support::storage::generator] traits
//! to provide strongly typed chain state queries over rpc.

#![warn(missing_docs)]

use codec::{DecodeAll, FullCodec, FullEncode};
use core::marker::PhantomData;
use frame_support::storage::generator::{StorageDoubleMap, StorageMap, StorageValue};
use jsonrpsee::core::Error as RpcError;
use sc_rpc_api::state::StateApiClient;
use serde::{de::DeserializeOwned, Serialize};
use sp_storage::{StorageData, StorageKey};

/// A typed query on chain state usable from an RPC client.
///
/// ```no_run
/// # use jsonrpsee::core::Error as RpcError;
/// # use jsonrpsee::ws_client::WsClientBuilder;
/// # use codec::Encode;
/// # use frame_support::traits::StorageInstance;
/// # use substrate_frame_rpc_support::StorageQuery;
/// # use sc_rpc_api::state::StateApiClient;
/// #
/// # // Hash would normally be <TestRuntime as frame_system::Config>::Hash, but we don't have
/// # // frame_system::Config implemented for TestRuntime. Here we just pretend.
/// # type Hash = ();
/// #
/// # struct TestRuntime;
/// #
/// pub type Loc = (i64, i64, i64);
/// pub type Block = u8;
///
/// // Note that all fields are marked pub.
/// pub use self::pallet::*;
///
/// #[frame_support::pallet]
/// mod pallet {
/// 	use super::*;
/// 	use frame_support::pallet_prelude::*;
///
/// 	#[pallet::pallet]
/// 	#[pallet::generate_store(pub(super) trait Store)]
/// 	pub struct Pallet<T>(PhantomData<T>);
///
/// 	#[pallet::config]
/// 	pub trait Config: frame_system::Config {}
///
/// 	pub struct LastActionIdPrefix;
/// 	impl StorageInstance for LastActionIdPrefix {
/// 		fn pallet_prefix() -> &'static str {
/// 			"TestRuntime"
/// 		}
/// 		const STORAGE_PREFIX: &'static str = "LastActionId";
/// 	}
/// 	pub type LastActionId = StorageValue<LastActionIdPrefix, u64, ValueQuery>;
///
/// 	pub struct VoxelsPrefix;
/// 	impl StorageInstance for VoxelsPrefix {
/// 		fn pallet_prefix() -> &'static str {
/// 			"TestRuntime"
/// 		}
/// 		const STORAGE_PREFIX: &'static str = "Voxels";
/// 	}
/// 	pub type Voxels = StorageMap<VoxelsPrefix, Blake2_128Concat, Loc, Block>;
///
/// 	pub struct ActionsPrefix;
/// 	impl StorageInstance for ActionsPrefix {
/// 		fn pallet_prefix() -> &'static str {
/// 			"TestRuntime"
/// 		}
/// 		const STORAGE_PREFIX: &'static str = "Actions";
/// 	}
/// 	pub type Actions = StorageMap<ActionsPrefix, Blake2_128Concat, u64, Loc>;
///
/// 	pub struct PrefabPrefix;
/// 	impl StorageInstance for PrefabPrefix {
/// 		fn pallet_prefix() -> &'static str {
/// 			"TestRuntime"
/// 		}
/// 		const STORAGE_PREFIX: &'static str = "Prefab";
/// 	}
/// 	pub type Prefab = StorageDoubleMap<
/// 		PrefabPrefix,
/// 		Blake2_128Concat, u128,
/// 		Blake2_128Concat, (i8, i8, i8), Block
/// 	>;
/// }
///
/// #[tokio::main]
/// async fn main() -> Result<(), RpcError> {
///     let cl = WsClientBuilder::default().build("ws://[::1]:9944").await?;
///
///     let q = StorageQuery::value::<LastActionId>();
///     let hash = None::<Hash>;
///     let _: Option<u64> = q.get(&cl, hash).await?;
///
///     let q = StorageQuery::map::<Voxels, _>((0, 0, 0));
///     let _: Option<Block> = q.get(&cl, hash).await?;
///
///     let q = StorageQuery::map::<Actions, _>(12);
///     let _: Option<Loc> = q.get(&cl, hash).await?;
///
///     let q = StorageQuery::double_map::<Prefab, _, _>(3, (0, 0, 0));
///     let _: Option<Block> = q.get(&cl, hash).await?;
///
///     Ok(())
/// }
/// ```
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct StorageQuery<V> {
	key: StorageKey,
	_spook: PhantomData<V>,
}

impl<V: FullCodec> StorageQuery<V> {
	/// Create a storage query for a StorageValue.
	pub fn value<St: StorageValue<V>>() -> Self {
		Self { key: StorageKey(St::storage_value_final_key().to_vec()), _spook: PhantomData }
	}

	/// Create a storage query for a value in a StorageMap.
	pub fn map<St: StorageMap<K, V>, K: FullEncode>(key: K) -> Self {
		Self { key: StorageKey(St::storage_map_final_key(key)), _spook: PhantomData }
	}

	/// Create a storage query for a value in a StorageDoubleMap.
	pub fn double_map<St: StorageDoubleMap<K1, K2, V>, K1: FullEncode, K2: FullEncode>(
		key1: K1,
		key2: K2,
	) -> Self {
		Self { key: StorageKey(St::storage_double_map_final_key(key1, key2)), _spook: PhantomData }
	}

	/// Send this query over RPC, await the typed result.
	///
	/// Hash should be <YourRuntime as frame::Config>::Hash.
	///
	/// # Arguments
	///
	/// state_client represents a connection to the RPC server.
	///
	/// block_index indicates the block for which state will be queried. A value of None indicates
	/// the latest block.
	pub async fn get<Hash, StateClient>(
		self,
		state_client: &StateClient,
		block_index: Option<Hash>,
	) -> Result<Option<V>, RpcError>
	where
		Hash: Send + Sync + 'static + DeserializeOwned + Serialize,
		StateClient: StateApiClient<Hash> + Sync,
	{
		let opt: Option<StorageData> = state_client.storage(self.key, block_index).await?;
		opt.map(|encoded| V::decode_all(&mut &encoded.0[..]))
			.transpose()
			.map_err(|decode_err| RpcError::Custom(decode_err.to_string()))
	}
}
