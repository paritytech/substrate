use core::fmt::Debug;

use async_std;
use codec::{Decode, Encode};
use hash_db::Hasher;
use jsonrpsee::http_client::{HttpClient, HttpClientBuilder};
use log;
use serde::{de::DeserializeOwned, Serialize};
use sp_core::storage::{ChildInfo, StateVersion};
use sp_state_machine::{
	backend::AsTrieBackend, Backend, ChildStorageCollection, DefaultError, InMemoryBackend,
	MemoryDB, StateMachineStats, StorageCollection, StorageIterator, StorageKey, StorageValue,
	TrieBackend, UsageInfo,
};
use sp_trie::HashKey;
use tokio::runtime::Runtime;

pub(crate) const LOG_TARGET: &str = "on-demand-backend";

pub struct OnDemandBackend<H>
where
	H: Hasher + 'static,
	H::Out: Ord + 'static + codec::Codec + DeserializeOwned + Serialize,
{
	// TODO: make this an LRU cache
	pub cache: InMemoryBackend<H>,
	http_client: HttpClient,
	at: Option<H::Out>,
}

impl<H> Debug for OnDemandBackend<H>
where
	H: Hasher + 'static,
	H::Out: Ord + 'static + codec::Codec + DeserializeOwned + Serialize,
{
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		write!(f, "OnDemandBackend")
	}
}

impl<H> OnDemandBackend<H>
where
	H: Hasher + 'static,
	H::Out: Ord + 'static + codec::Codec + DeserializeOwned + Serialize,
{
	pub fn new(rpc_uri: String, at: Option<H::Out>) -> Result<Self, &'static str> {
		let http_client = HttpClientBuilder::default()
			.max_request_body_size(u32::MAX)
			.request_timeout(std::time::Duration::from_secs(60 * 5))
			.build(rpc_uri)
			.map_err(|e| {
				log::error!(target: LOG_TARGET, "error: {:?}", e);
				"failed to build http client"
			})?;

		Ok(Self { http_client, cache: InMemoryBackend::default(), at })
	}

	fn storage_remote(&self, key: &[u8]) -> Result<Option<StorageValue>, DefaultError> {
		// TODO: figure out how to do this without spawning a new thread each remote storage req :')
		log::info!("fetching key from backend!!!!!!!!!!!!!!!!!!!!!");
		async_std::task::block_on(substrate_rpc_client::StateApi::<H::Out>::storage(
			&self.http_client,
			sp_core::storage::StorageKey(key.to_vec()),
			self.at.clone(),
		))
		.map(|r| r.map(|x| x.0))
		.map_err(|e| format!("{:?}", e))
	}
}

impl<H> Backend<H> for OnDemandBackend<H>
where
	H: Hasher + 'static,
	H::Out: Ord + 'static + codec::Codec + DeserializeOwned + Serialize,
{
	type Error = <InMemoryBackend<H> as Backend<H>>::Error;
	type Transaction = <InMemoryBackend<H> as Backend<H>>::Transaction;
	type TrieBackendStorage = <InMemoryBackend<H> as Backend<H>>::TrieBackendStorage;
	type RawIter = RawIter<H>;

	fn raw_iter(&self, _args: sp_state_machine::IterArgs) -> Result<Self::RawIter, Self::Error> {
		todo!()
	}

	fn storage(&self, key: &[u8]) -> Result<Option<StorageValue>, Self::Error> {
		self.cache.storage(key).map(|opt| {
			opt.or_else(|| {
				self.storage_remote(key).unwrap().map(|v| {
					let inner = unsafe {
						let x = &self.cache as *const InMemoryBackend<H>;
						let y = x as *mut InMemoryBackend<H>;
						&mut *y
					};
					inner.insert(
						vec![(None, vec![(key.to_vec(), Some(v.clone()))])],
						StateVersion::V1,
					);
					v
				})
			})
		})
	}

	/// Get keyed storage value hash or None if there is nothing associated.
	fn storage_hash(&self, key: &[u8]) -> Result<Option<<H as Hasher>::Out>, Self::Error> {
		self.storage(key).map(|o| o.map(|v| H::hash(&v)))
	}

	/// Get keyed child storage or None if there is nothing associated.
	fn child_storage(
		&self,
		_child_info: &ChildInfo,
		_key: &[u8],
	) -> Result<Option<StorageValue>, Self::Error> {
		todo!("check inner_backend, else call remote");
	}

	/// Get child keyed storage value hash or None if there is nothing associated.
	fn child_storage_hash(
		&self,
		_child_info: &ChildInfo,
		_key: &[u8],
	) -> Result<Option<<H as Hasher>::Out>, Self::Error> {
		todo!("check inner_backend, else call remote");
	}

	/// true if a key exists in storage.
	fn exists_storage(&self, _key: &[u8]) -> Result<bool, Self::Error> {
		todo!("check local, else check remote")
	}

	/// true if a key exists in child storage.
	fn exists_child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<bool, Self::Error> {
		Ok(self.child_storage_hash(child_info, key)?.is_some())
	}

	/// Return the next key in storage in lexicographic order or `None` if there is no value.
	fn next_storage_key(&self, key: &[u8]) -> Result<Option<StorageKey>, Self::Error> {
		// question: Kian's TODO said to check remote for the next storage key. is this necessary?
		// i don't really know what the storage keys are used for.
		self.cache.next_storage_key(key)
	}

	/// Return the next key in child storage in lexicographic order or `None` if there is no value.
	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<StorageKey>, Self::Error> {
		// question: Kian's TODO said to check remote for the next storage key. is this necessary?
		// i don't really know what the storage keys are used for.
		self.cache.next_child_storage_key(child_info, key)
	}

	/// Calculate the storage root, with given delta over what is already stored in the backend, and
	/// produce a "transaction" that can be used to commit.
	///
	/// Does not include child storage updates.
	fn storage_root<'a>(
		&self,
		_delta: impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>,
		_state_version: StateVersion,
	) -> (<H as Hasher>::Out, Self::Transaction)
	where
		<H as Hasher>::Out: Ord + Decode + Encode,
	{
		// PLACEHOLDER IMPLEMENTATION
		(self.cache.root().clone(), Default::default())
	}

	/// Calculate the child storage root, with given delta over what is already stored in the
	/// backend, and produce a "transaction" that can be used to commit.
	///
	/// The second argument is true if child storage root equals default storage root.
	fn child_storage_root<'a>(
		&self,
		_child_info: &ChildInfo,
		_delta: impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>,
		_state_version: StateVersion,
	) -> (<H as Hasher>::Out, bool, Self::Transaction)
	where
		<H as Hasher>::Out: Ord,
	{
		todo!();
	}

	fn pairs<'a>(
		&'a self,
		_args: sp_state_machine::IterArgs,
	) -> Result<sp_state_machine::PairsIter<'a, H, Self::RawIter>, Self::Error> {
		todo!()
	}

	/// Get all keys with given prefix
	fn keys<'a>(
		&'a self,
		_args: sp_state_machine::IterArgs,
	) -> Result<sp_state_machine::KeysIter<'a, H, Self::RawIter>, Self::Error> {
		todo!()
	}

	/// Calculate the storage root, with given delta over what is already stored
	/// in the backend, and produce a "transaction" that can be used to commit.
	/// Does include child storage updates.
	fn full_storage_root<'a>(
		&self,
		delta: impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>,
		child_deltas: impl Iterator<
			Item = (&'a ChildInfo, impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>),
		>,
		state_version: StateVersion,
	) -> (<H as Hasher>::Out, Self::Transaction)
	where
		<H as Hasher>::Out: Ord + Encode + Decode,
	{
		let mut txs: Self::Transaction = Default::default();
		let mut child_roots: Vec<_> = Default::default();
		// child first
		for (child_info, child_delta) in child_deltas {
			let (child_root, empty, child_txs) =
				self.child_storage_root(child_info, child_delta, state_version);
			let prefixed_storage_key = child_info.prefixed_storage_key();
			txs.consolidate(child_txs);
			if empty {
				child_roots.push((prefixed_storage_key.into_inner(), None));
			} else {
				child_roots.push((prefixed_storage_key.into_inner(), Some(child_root.encode())));
			}
		}
		let (root, parent_txs) = self.storage_root(
			delta
				.map(|(k, v)| (k, v.as_ref().map(|v| &v[..])))
				.chain(child_roots.iter().map(|(k, v)| (&k[..], v.as_ref().map(|v| &v[..])))),
			state_version,
		);
		txs.consolidate(parent_txs);
		(root, txs)
	}

	/// Register stats from overlay of state machine.
	///
	/// By default nothing is registered.
	fn register_overlay_stats(&self, _stats: &StateMachineStats) {
		// todo!();
	}

	/// Query backend usage statistics (i/o, memory)
	///
	/// Not all implementations are expected to be able to do this. In the case when they don't,
	/// empty statistics is returned.
	fn usage_info(&self) -> UsageInfo {
		unimplemented!()
	}

	/// Wipe the state database.
	fn wipe(&self) -> Result<(), Self::Error> {
		unimplemented!()
	}

	/// Commit given transaction to storage.
	fn commit(
		&self,
		_: <H as Hasher>::Out,
		_: Self::Transaction,
		_: StorageCollection,
		_: ChildStorageCollection,
	) -> Result<(), Self::Error> {
		unimplemented!()
	}

	/// Get the read/write count of the db
	fn read_write_count(&self) -> (u32, u32, u32, u32) {
		unimplemented!()
	}

	/// Get the read/write count of the db
	fn reset_read_write_count(&self) {
		unimplemented!()
	}

	/// Estimate proof size
	fn proof_size(&self) -> Option<u32> {
		unimplemented!()
	}

	/// Extend storage info for benchmarking db
	fn get_read_and_written_keys(&self) -> Vec<(Vec<u8>, u32, u32, bool)> {
		unimplemented!()
	}
}

pub struct RawIter<H>
where
	H: Hasher + 'static,
	H::Out: Ord + 'static + codec::Codec + DeserializeOwned + Serialize,
{
	inner: <InMemoryBackend<H> as Backend<H>>::RawIter,
}

impl<H> StorageIterator<H> for RawIter<H>
where
	H: Hasher + 'static,
	H::Out: Ord + 'static + codec::Codec + DeserializeOwned + Serialize,
{
	type Backend = OnDemandBackend<H>;
	type Error = <InMemoryBackend<H> as Backend<H>>::Error;

	fn next_key(&mut self, backend: &Self::Backend) -> Option<Result<StorageKey, Self::Error>> {
		self.inner.next_key(&backend.cache)
	}

	fn next_pair(
		&mut self,
		backend: &Self::Backend,
	) -> Option<Result<(StorageKey, StorageValue), Self::Error>> {
		self.inner.next_pair(&backend.cache)
	}

	fn was_complete(&self) -> bool {
		self.inner.was_complete()
	}
}

impl<H> AsTrieBackend<H> for OnDemandBackend<H>
where
	H: Hasher + 'static,
	H::Out: Ord + 'static + codec::Codec + DeserializeOwned + Serialize,
{
	type TrieBackendStorage = <InMemoryBackend<H> as Backend<H>>::TrieBackendStorage;

	fn as_trie_backend(
		&self,
	) -> &sp_state_machine::TrieBackend<
		Self::TrieBackendStorage,
		H,
		sp_trie::cache::LocalTrieCache<H>,
	> {
		&self.cache
	}
}
