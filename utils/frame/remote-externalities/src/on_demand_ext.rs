use std::collections::BTreeMap;

use sp_runtime::StorageChild;
use sp_state_machine::{Backend, StorageValue, OverlayedChanges, StorageTransactionCache};
use sp_storage::ChildInfo;

use crate::backend::HasherT;


pub struct OnDemandExternalities<H, B>
where
	H: HasherT,
	H::Out: codec::Codec + Ord,
{
	/// The overlay changed storage.
	overlay: OverlayedChanges,
	storage_transaction_cache: StorageTransactionCache<<B as Backend<H>>::Transaction, H>,
	/// Storage backend.
	pub backend: B,
	/// Extensions.
	pub extensions: Extensions,
	/// State version to use during tests.
	pub state_version: StateVersion,
}

#[derive(Debug)]
pub struct RemoteExternalitiesBackendSimple {
	rpc: substrate_rpc_client::WsClient,
	top: BTreeMap<Vec<u8>, Vec<u8>>,
	children: BTreeMap<Vec<u8>, StorageChild>,
}

impl RemoteExternalitiesBackendSimple {
	pub fn new(rpc: substrate_rpc_client::WsClient) -> Self {
		Self {
			rpc,
			top: Default::default(),
			children: Default::default(),
		}
	}
}

impl<H: HasherT> Backend<H> for RemoteExternalitiesBackendSimple {
	type Error = &'static str;
	type Transaction = sp_trie::MemoryDB<H>;
	type TrieBackendStorage = sp_trie::MemoryDB<H>;

	fn storage(&self, key: &[u8]) -> Result<Option<StorageValue>, Self::Error> {
		todo!();
	}

	/// Get keyed storage value hash or None if there is nothing associated.
	fn storage_hash(&self, key: &[u8]) -> Result<Option<H::Out>, Self::Error> {
		todo!();
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
		todo!();
	}

	fn next_storage_key(&self, key: &[u8]) -> Result<Option<StorageKey>, Self::Error> {
		todo!("check local, else check remote")
	}

	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<StorageKey>, Self::Error> {
		todo!("check local, else check remote")
	}

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

	fn apply_to_keys_while<F: FnMut(&[u8]) -> bool>(
		&self,
		child_info: Option<&ChildInfo>,
		prefix: Option<&[u8]>,
		start_at: Option<&[u8]>,
		f: F,
	) {
		unimplemented!()
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], mut f: F) {
		todo!();
	}

	fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], f: F) {
		unimplemented!()
	}

	fn for_child_keys_with_prefix<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
		prefix: &[u8],
		f: F,
	) {
		unimplemented!()
	}

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

	fn pairs(&self) -> Vec<(StorageKey, StorageValue)> {
		todo!("oh boy");
	}

	fn keys(&self, prefix: &[u8]) -> Vec<StorageKey> {
		todo!();
	}

	fn child_keys(&self, child_info: &ChildInfo, prefix: &[u8]) -> Vec<StorageKey> {
		todo!();
	}

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
		todo!();
	}

	fn register_overlay_stats(&self, _stats: &StateMachineStats) {
		todo!();
	}

	fn usage_info(&self) -> UsageInfo {
		unimplemented!()
	}

	fn wipe(&self) -> Result<(), Self::Error> {
		unimplemented!()
	}

	fn commit(
		&self,
		_: H::Out,
		_: Self::Transaction,
		_: StorageCollection,
		_: ChildStorageCollection,
	) -> Result<(), Self::Error> {
		unimplemented!()
	}

	fn read_write_count(&self) -> (u32, u32, u32, u32) {
		unimplemented!()
	}

	fn reset_read_write_count(&self) {
		unimplemented!()
	}

	fn get_whitelist(&self) -> Vec<TrackedStorageKey> {
		Default::default()
	}

	fn set_whitelist(&self, _: Vec<TrackedStorageKey>) {}

	fn proof_size(&self) -> Option<u32> {
		unimplemented!()
	}

	fn get_read_and_written_keys(&self) -> Vec<(Vec<u8>, u32, u32, bool)> {
		unimplemented!()
	}
}
