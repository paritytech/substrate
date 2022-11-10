use codec::{Decode, Encode};
use sp_core::{storage, storage::ChildInfo};
use sp_runtime::DeserializeOwned;
use sp_state_machine::{
	backend::Hasher, Backend, ChildStorageCollection, InMemoryBackend, StateMachineStats,
	StorageCollection, StorageKey, StorageValue, UsageInfo,
};
use sp_storage::{StateVersion, TrackedStorageKey};
use std::marker::PhantomData;

pub struct RemoteExternalitiesBackend<H: Hasher> {
	inner_backend: InMemoryBackend<H>,
	rpc: substrate_rpc_client::WsClient,
	runtime: tokio::runtime::Runtime,
	at: Option<H>,
	_marker: PhantomData<H>,
}

impl<H: Hasher> std::fmt::Debug for RemoteExternalitiesBackend<H> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "RemoteExternalitiesBackend")
	}
}

pub trait HasherT: Hasher + Clone + serde::ser::Serialize + DeserializeOwned + 'static {}
impl<T: Hasher + Clone + serde::ser::Serialize + DeserializeOwned + 'static> HasherT for T {}

impl<H: HasherT>
	RemoteExternalitiesBackend<H>
{
	fn storage_remote(
		&self,
		key: &[u8],
	) -> Result<Option<StorageValue>, sp_state_machine::DefaultError> {
		self.runtime
			.block_on(substrate_rpc_client::StateApi::<H>::storage(
				&self.rpc,
				sp_core::storage::StorageKey(key.to_vec()),
				self.at.clone(),
			))
			.map(|r| r.map(|x| x.0))
			.map_err(|e| format!("{:?}", e))
	}
}

impl<H: HasherT> Backend<H> for RemoteExternalitiesBackend<H>
where
	<H as Hasher>::Out: Ord + Decode + Encode,
{
	/// An error type when fetching data is not possible.
	type Error = <InMemoryBackend<H> as Backend<H>>::Error;

	/// Storage changes to be applied if committing
	type Transaction = <InMemoryBackend<H> as Backend<H>>::Transaction;

	/// Type of trie backend storage.
	type TrieBackendStorage = <InMemoryBackend<H> as Backend<H>>::TrieBackendStorage;

	/// Get keyed storage or None if there is nothing associated.
	fn storage(&self, key: &[u8]) -> Result<Option<StorageValue>, Self::Error> {
		self.inner_backend
			.storage(key)
			.map(|opt| opt.or_else(|| self.storage_remote(key).unwrap()))
	}

	/// Get keyed storage value hash or None if there is nothing associated.
	fn storage_hash(&self, key: &[u8]) -> Result<Option<H::Out>, Self::Error> {
		todo!("check inner_backend, else call remote");
	}

	/// Get keyed child storage or None if there is nothing associated.
	fn child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<StorageValue>, Self::Error> {
		todo!("check inner_backend, else call remote");
	}

	/// Get child keyed storage value hash or None if there is nothing associated.
	fn child_storage_hash(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<H::Out>, Self::Error> {
		todo!("check inner_backend, else call remote");
	}

	/// true if a key exists in storage.
	fn exists_storage(&self, key: &[u8]) -> Result<bool, Self::Error> {
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
		todo!("check local, else check remote")
	}

	/// Return the next key in child storage in lexicographic order or `None` if there is no value.
	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<StorageKey>, Self::Error> {
		todo!("check local, else check remote")
	}

	/// Iterate over storage starting at key, for a given prefix and child trie. Aborts as soon as
	/// `f` returns false. Warning, this fails at first error when usual iteration skips errors. If
	/// `allow_missing` is true, iteration stops when it reaches a missing trie node. Otherwise an
	/// error is produced.
	///
	/// Returns `true` if trie end is reached.
	fn apply_to_key_values_while<F: FnMut(Vec<u8>, Vec<u8>) -> bool>(
		&self,
		child_info: Option<&ChildInfo>,
		prefix: Option<&[u8]>,
		start_at: Option<&[u8]>,
		f: F,
		allow_missing: bool,
	) -> Result<bool, Self::Error> {
		unimplemented!()
	}

	/// Retrieve all entries keys of storage and call `f` for each of those keys.
	/// Aborts as soon as `f` returns false.
	fn apply_to_keys_while<F: FnMut(&[u8]) -> bool>(
		&self,
		child_info: Option<&ChildInfo>,
		prefix: Option<&[u8]>,
		start_at: Option<&[u8]>,
		f: F,
	) {
		unimplemented!()
	}

	/// Retrieve all entries keys which start with the given prefix and
	/// call `f` for each of those keys.
	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], mut f: F) {
		self.for_key_values_with_prefix(prefix, |k, _v| f(k))
	}

	/// Retrieve all entries keys and values of which start with the given prefix and
	/// call `f` for each of those keys.
	fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], f: F) {
		unimplemented!()
	}

	/// Retrieve all child entries keys which start with the given prefix and
	/// call `f` for each of those keys.
	fn for_child_keys_with_prefix<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
		prefix: &[u8],
		f: F,
	) {
		unimplemented!()
	}

	/// Calculate the storage root, with given delta over what is already stored in the backend, and
	/// produce a "transaction" that can be used to commit.
	///
	/// Does not include child storage updates.
	fn storage_root<'a>(
		&self,
		delta: impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>,
		state_version: StateVersion,
	) -> (H::Out, Self::Transaction)
	where
		H::Out: Ord,
	{
		todo!();
	}

	/// Calculate the child storage root, with given delta over what is already stored in the
	/// backend, and produce a "transaction" that can be used to commit.
	///
	/// The second argument is true if child storage root equals default storage root.
	fn child_storage_root<'a>(
		&self,
		child_info: &ChildInfo,
		delta: impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>,
		state_version: StateVersion,
	) -> (H::Out, bool, Self::Transaction)
	where
		H::Out: Ord,
	{
		todo!();
	}

	/// Get all key/value pairs into a Vec.
	fn pairs(&self) -> Vec<(StorageKey, StorageValue)> {
		todo!("oh boy");
	}

	/// Get all keys with given prefix
	fn keys(&self, prefix: &[u8]) -> Vec<StorageKey> {
		let mut all = Vec::new();
		self.for_keys_with_prefix(prefix, |k| all.push(k.to_vec()));
		all
	}

	/// Get all keys of child storage with given prefix
	fn child_keys(&self, child_info: &ChildInfo, prefix: &[u8]) -> Vec<StorageKey> {
		let mut all = Vec::new();
		self.for_child_keys_with_prefix(child_info, prefix, |k| all.push(k.to_vec()));
		all
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
	) -> (H::Out, Self::Transaction)
	where
		H::Out: Ord + Encode,
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
		todo!();
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
		_: H::Out,
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

	/// Get the whitelist for tracking db reads/writes
	fn get_whitelist(&self) -> Vec<TrackedStorageKey> {
		Default::default()
	}

	/// Update the whitelist for tracking db reads/writes
	fn set_whitelist(&self, _: Vec<TrackedStorageKey>) {}

	/// Estimate proof size
	fn proof_size(&self) -> Option<u32> {
		unimplemented!()
	}

	/// Extend storage info for benchmarking db
	fn get_read_and_written_keys(&self) -> Vec<(Vec<u8>, u32, u32, bool)> {
		unimplemented!()
	}
}

#[cfg(test)]
mod tests {
	use sp_core::H256;
use sp_runtime::traits::BlakeTwo256;
use sp_state_machine::TrieBackendBuilder;

use crate::RemoteExternalities;

use super::*;

	#[tokio::test(flavor = "multi_thread")]
	async fn can_build_and_execute_externalities() {
		let rpc = substrate_rpc_client::ws_client("wss://rpc.polkadot.io:443").await.unwrap();
		let runtime = tokio::runtime::Runtime::new().unwrap();
		let backend = RemoteExternalitiesBackend::<BlakeTwo256> {
			at: None,
			rpc,
			runtime,
			inner_backend: TrieBackendBuilder::new(Default::default(), Default::default()).build(),
			_marker: Default::default(),
		};
	}


}
