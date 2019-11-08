//! Combines [substrate_rpc_api::state::StateClient] with [srml_support::storage::generator] traits
//! to provide strongly typed chain state queries over rpc.

use core::marker::PhantomData;
use futures::compat::Future01CompatExt;
use jsonrpc_client_transports::RpcError;
use parity_scale_codec::{DecodeAll, FullCodec, FullEncode};
use serde::{de::DeserializeOwned, Serialize};
use srml_support::storage::generator::{
    StorageDoubleMap, StorageLinkedMap, StorageMap, StorageValue,
};
use substrate_primitives_storage::{StorageData, StorageKey};
use substrate_rpc_api::state::StateClient;

/// A typed query on chain state usable from an RPC client.
///
/// ```no_run
/// # use srml_support::{decl_storage, decl_module};
/// # use parity_scale_codec::Encode;
/// # use srml_system::Trait;
/// # use substrate_rpc_custom::StorageQuery;
/// # use substrate_rpc_api::state::StateClient;
/// # use jsonrpc_client_transports::transports::http;
/// # use jsonrpc_client_transports::RpcError;
/// # use futures::compat::Compat;
/// # use futures::future::FutureExt;
/// # use futures::compat::Future01CompatExt;
/// #
/// # // Hash would normally be <TestRuntime as srml_system::Trait>::Hash, but we don't have
/// # // srml_system::Trait implemented for TestRuntime. Here we just pretend.
/// # type Hash = ();
/// #
/// # fn main() -> Result<(), RpcError> {
/// #     tokio::runtime::Runtime::new().unwrap().block_on(Compat::new(test().boxed()))
/// # }
/// #
/// # struct TestRuntime;
/// #
/// # decl_module! {
///	#     pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
/// # }
/// #
/// pub type Loc = (i64, i64, i64);
/// pub type Block = u8;
///
/// // Note that all fields are marked pub.
/// decl_storage! {
///     trait Store for Module<T: Trait> as TestRuntime {
///         pub LastActionId: u64;
///         pub Voxels: map Loc => Block;
///         pub Actions: linked_map u64 => Loc;
///         pub Prefab: double_map u128, blake2_256((i8, i8, i8)) => Block;
///     }
/// }
///
/// # async fn test() -> Result<(), RpcError> {
/// let conn = http::connect("http://[::1]:9933").compat().await?;
/// let cl = StateClient::<Hash>::new(conn);
///
/// let q = StorageQuery::value::<LastActionId>();
/// let _: Option<u64> = q.get(&cl, None).await?;
///
/// let q = StorageQuery::map::<Voxels, _>((0, 0, 0));
/// let _: Option<Block> = q.get(&cl, None).await?;
///
/// let q = StorageQuery::linked_map::<Actions, _>(12);
/// let _: Option<Loc> = q.get(&cl, None).await?;
///
/// let q = StorageQuery::double_map::<Prefab, _, _>(3, (0, 0, 0));
/// let _: Option<Block> = q.get(&cl, None).await?;
/// #
/// # Ok(())
/// # }
/// ```
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct StorageQuery<V> {
    key: StorageKey,
    _spook: PhantomData<V>,
}

impl<V: FullCodec> StorageQuery<V> {
    /// Create a storage query for a StorageValue.
    pub fn value<St: StorageValue<V>>() -> Self {
        Self {
            key: StorageKey(St::storage_value_final_key().to_vec()),
            _spook: PhantomData,
        }
    }

    /// Create a storage query for a value in a StorageMap.
    pub fn map<St: StorageMap<K, V>, K: FullEncode>(key: K) -> Self {
        Self {
            key: StorageKey(St::storage_map_final_key(key).as_ref().to_vec()),
            _spook: PhantomData,
        }
    }

    /// Create a storage query for a value in a StorageLinkedMap.
    pub fn linked_map<St: StorageLinkedMap<K, V>, K: FullCodec>(key: K) -> Self {
        Self {
            key: StorageKey(St::storage_linked_map_final_key(key).as_ref().to_vec()),
            _spook: PhantomData,
        }
    }

    /// Create a storage query for a value in a StorageDoubleMap.
    pub fn double_map<St: StorageDoubleMap<K1, K2, V>, K1: FullEncode, K2: FullEncode>(
        key1: K1,
        key2: K2,
    ) -> Self {
        Self {
            key: StorageKey(St::storage_double_map_final_key(key1, key2)),
            _spook: PhantomData,
        }
    }

    /// Send this query over RPC, await the typed result.
    ///
    /// Hash should be <YourRuntime as srml::Trait>::Hash.
    ///
    /// # Arguments
    ///
    /// state_client represents a connection to the RPC server.
    ///
    /// block_index indicates the block for which state will be queried. A value of None indicates the
    /// latest block.
    pub async fn get<Hash: Send + Sync + 'static + DeserializeOwned + Serialize>(
        self,
        state_client: &StateClient<Hash>,
        block_index: Option<Hash>,
    ) -> Result<Option<V>, RpcError> {
        let opt: Option<StorageData> = state_client.storage(self.key, block_index).compat().await?;
        opt.map(|encoded| V::decode_all(&encoded.0))
            .transpose()
            .map_err(|decode_err| RpcError::Other(decode_err.into()))
    }
}
