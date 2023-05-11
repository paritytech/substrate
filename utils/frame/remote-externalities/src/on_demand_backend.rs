use async_std;
use codec::{Decode, Encode};
use core::fmt::Debug;
use hash_db::Hasher;
use log;
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use sp_core::{
	hexdisplay::HexDisplay,
	storage::{ChildInfo, StateVersion, StorageData, StorageKey},
	H256,
};
use sp_state_machine::{
	backend::AsTrieBackend, Backend, ChildStorageCollection, DefaultError, InMemoryBackend,
	IterArgs, StateMachineStats, StorageCollection, StorageIterator, StorageValue, UsageInfo,
};
use std::{
	sync::{mpsc, Arc},
	time::Duration,
};
use substrate_rpc_client::{WsClient, WsClientBuilder};

#[derive(Debug, Serialize, Deserialize)]
struct StorageJsonRpcResponse {
	result: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
struct KeysJsonRpcResponse {
	result: Option<Vec<String>>,
}

pub(crate) const LOG_TARGET: &str = "on-demand-backend";

pub struct OnDemandBackend<H>
where
	H: Hasher + 'static,
	H::Out: Ord + 'static + codec::Codec + DeserializeOwned + Serialize,
{
	// TODO: make this an LRU cache
	pub cache: InMemoryBackend<H>,
	ws_client: Arc<WsClient>,
	// TODO: make this a generic type
	at: Arc<Option<H256>>,
	// TODO: we still create a new Runtime inside the thread each time we use it,
	// there's probably a cleaner way to do the async handling.
	pool: rayon::ThreadPool,
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
	pub fn new(rpc_uri: String, at: Option<H256>) -> Result<Self, &'static str> {
		let ws_client = async_std::task::block_on(
			WsClientBuilder::default()
				.max_request_body_size(u32::MAX)
				.connection_timeout(Duration::from_secs(5))
				.build(rpc_uri),
		)
		.unwrap(); // TODO: Handle error

		let pool = rayon::ThreadPoolBuilder::new().num_threads(1).build().unwrap(); // TODO: Handle error
		Ok(Self {
			ws_client: Arc::new(ws_client),
			cache: InMemoryBackend::default(),
			at: Arc::new(at),
			pool,
		})
	}

	fn storage_remote(&self, key: &[u8]) -> Result<Option<StorageData>, DefaultError> {
		// TODO: better error handling

		log::debug!(
			target: LOG_TARGET,
			"fetching storage from remote. key: {:?}, at: {}",
			HexDisplay::from(&key).to_string(),
			HexDisplay::from(&self.at.unwrap().encode().as_slice()).to_string()
		);

		let ws_client = self.ws_client.clone();
		let at = self.at.clone();
		let key = key.to_vec();

		let (tx, rx) = mpsc::channel();
		self.pool.spawn(move || {
			let rt = tokio::runtime::Runtime::new().unwrap();
			let result = rt
				.block_on(substrate_rpc_client::StateApi::<H256>::storage(
					ws_client.as_ref(),
					StorageKey(key),
					at.as_ref().clone(),
				))
				.unwrap();

			tx.send(result).unwrap();
		});

		let result = match rx.recv().unwrap() {
			Some(storage_data) => {
				log::debug!(target: LOG_TARGET, "got result: {:?}", HexDisplay::from(&storage_data.0));
				return Ok(Some(storage_data))
			},
			None => {
				log::debug!(target: LOG_TARGET, "got result: None");
				Ok(None)
			},
		};
		result
	}

	fn storage_keys_paged_remote(
		&self,
		prefix: Option<&[u8]>,
		count: u32,
		start_key: Option<&[u8]>,
	) -> Result<Vec<StorageKey>, DefaultError> {
		// TODO: better error handling

		log::debug!(
			target: LOG_TARGET,
			"fetching key from remote. prefix: {:?}, start_key: {:?}, at: {}",
			prefix.map(|s| HexDisplay::from(&s).to_string()),
			start_key.map(|s| HexDisplay::from(&s).to_string()),
			HexDisplay::from(&self.at.unwrap().encode().as_slice()).to_string()
		);

		let ws_client = self.ws_client.clone();
		let prefix = prefix.map(|p| StorageKey(p.to_vec()));
		let start_key = start_key.map(|p| StorageKey(p.to_vec()));
		let at = self.at.clone();

		let (tx, rx) = mpsc::channel();
		self.pool.spawn(move || {
			let rt = tokio::runtime::Runtime::new().unwrap();
			let result = rt
				.block_on(substrate_rpc_client::StateApi::<H256>::storage_keys_paged(
					ws_client.as_ref(),
					prefix,
					count,
					start_key,
					at.as_ref().clone(),
				))
				.unwrap();

			tx.send(result).unwrap();
		});

		let result = rx.recv().unwrap();
		log::debug!(target: LOG_TARGET, "got result: {:?}", result.iter().map(|s| HexDisplay::from(s).to_string()).collect::<Vec<_>>());
		Ok(result)
	}

	fn storage_child_keys_paged_remote(
		&self,
		child_info: &ChildInfo,
		prefix: Option<&[u8]>,
		count: u32,
		start_key: Option<&[u8]>,
	) -> Result<Vec<StorageKey>, DefaultError> {
		// TODO: better error handling

		log::debug!(
			target: LOG_TARGET,
			"fetching child key from remote. child_info_prefixed_storage_key: {:?} prefix: {:?}, start_key: {:?}, at: {}",
			child_info.prefixed_storage_key(),
			prefix.map(|s| HexDisplay::from(&s).to_string()),
			start_key.map(|s| HexDisplay::from(&s).to_string()),
			HexDisplay::from(&self.at.unwrap().encode().as_slice()).to_string()
		);

		let ws_client = self.ws_client.clone();
		let prefix = prefix.map(|p| StorageKey(p.to_vec()));
		let start_key = start_key.map(|p| StorageKey(p.to_vec()));
		let at = self.at.clone();
		let child_info_prefixed_storage_key = child_info.prefixed_storage_key().clone();

		let (tx, rx) = mpsc::channel();
		self.pool.spawn(move || {
			let rt = tokio::runtime::Runtime::new().unwrap();
			let result = rt
				.block_on(substrate_rpc_client::ChildStateApi::<H256>::storage_keys_paged(
					ws_client.as_ref(),
					child_info_prefixed_storage_key,
					prefix,
					count,
					start_key,
					at.as_ref().clone(),
				))
				.unwrap();

			tx.send(result).unwrap();
		});

		let result = rx.recv().unwrap();
		log::debug!(target: LOG_TARGET, "got result: {:?}", result.iter().map(|s| HexDisplay::from(s).to_string()));
		Ok(result)
	}
}

pub struct RawIter<H>
where
	H: Hasher + 'static,
	H::Out: Ord + 'static + codec::Codec + DeserializeOwned + Serialize,
{
	prefix: Option<Vec<u8>>,
	last_key: Option<Vec<u8>>,
	child_info: Option<ChildInfo>,
	_stop_on_incomplete_database: bool, // TODO: how to handle this?
	complete: bool,
	_phantom: std::marker::PhantomData<H>,
}

impl<H> RawIter<H>
where
	H: Hasher + 'static,
	H::Out: Ord + 'static + codec::Codec + DeserializeOwned + Serialize,
{
	pub fn new(
		prefix: Option<&[u8]>,
		child_info: Option<ChildInfo>,
		start_at: Option<&[u8]>,
		stop_on_incomplete_database: bool,
	) -> Self {
		Self {
			prefix: prefix.map(|slice| slice.to_vec()),
			child_info,
			last_key: start_at.map(|slice| slice.to_vec()),
			_stop_on_incomplete_database: stop_on_incomplete_database,
			complete: false,
			_phantom: Default::default(),
		}
	}
}

impl<H> StorageIterator<H> for RawIter<H>
where
	H: Hasher + 'static,
	H::Out: Ord + 'static + codec::Codec + DeserializeOwned + Serialize,
{
	type Backend = OnDemandBackend<H>;
	type Error = <OnDemandBackend<H> as Backend<H>>::Error;

	fn next_key(&mut self, backend: &Self::Backend) -> Option<Result<Vec<u8>, Self::Error>> {
		if self.complete {
			log::debug!(target: LOG_TARGET, "complete");
			return None
		}
		// TODO: optimistically fetch future keys here, so we don't need to go to the node every
		// single key
		// TODO: cleaner child key handling
		log::debug!(
			target: LOG_TARGET,
			"last key: {}",
			self.last_key
				.clone()
				.map(|s| HexDisplay::from(&s.as_slice()).to_string())
				.unwrap_or("None".to_string())
		);
		let binding = match &self.child_info {
			None => backend
				.storage_keys_paged_remote(
					self.prefix.as_ref().map(|v| v.as_slice()).clone(),
					1,
					self.last_key.as_ref().map(|v| v.as_slice()).clone(),
				)
				.unwrap(), // TODO: handle error
			Some(child_info) => backend
				.storage_child_keys_paged_remote(
					child_info,
					self.prefix.as_ref().map(|v| v.as_slice()).clone(),
					1,
					self.last_key.as_ref().map(|v| v.as_slice()).clone(),
				)
				.unwrap(), // TODO: handle error
		};
		let key = match binding.get(0) {
			Some(key) => key,
			None => {
				self.complete = true;
				return None
			},
		};
		self.last_key = Some(key.0.clone());
		log::debug!(
			target: LOG_TARGET,
			"set last key to: {}",
			self.last_key
				.clone()
				.map(|s| HexDisplay::from(&s.as_slice()).to_string())
				.unwrap_or("None".to_string())
		);
		Some(Ok(key.clone().0))
	}

	fn next_pair(&mut self, backend: &Self::Backend) -> Option<Result<(Vec<u8>, Vec<u8>), String>> {
		// TODO: optimistically fetch future pairs here, so we don't need to go to the node every
		// single key
		// TODO: better err handling
		let key = match self.next_key(backend) {
			Some(Ok(key)) => key,
			Some(Err(e)) => return Some(Err(format!("{:?}", e))),
			None => return None,
		};
		let value = match backend.storage(key.as_slice()) {
			Ok(Some(value)) => value,
			Ok(None) => return Some(Err("value not found".to_string())),
			Err(e) => return Some(Err(format!("{:?}", e))),
		};
		Some(Ok((key, value)))
	}

	fn was_complete(&self) -> bool {
		self.complete
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

	fn raw_iter(&self, args: IterArgs) -> Result<Self::RawIter, Self::Error> {
		// TODO: set `start_at` based on args.start_at_exclusive
		Ok(Self::RawIter::new(
			args.prefix,
			args.child_info,
			args.start_at,
			args.stop_on_incomplete_database,
		))
	}

	fn storage(&self, key: &[u8]) -> Result<Option<StorageValue>, Self::Error> {
		self.cache.storage(key).map(|opt| {
			opt.or_else(|| {
				// todo: remove this unwrap
				self.storage_remote(key).unwrap().map(|v| {
					log::debug!(target: LOG_TARGET, "got value: {:?}", HexDisplay::from(&v.0.as_slice()));
					// TODO: cache value here
					let inner = unsafe {
						let x = &self.cache as *const InMemoryBackend<H>;
						let y = x as *mut InMemoryBackend<H>;
						&mut *y
					};
					inner.insert(
						vec![(None, vec![(key.to_vec(), Some(v.0.clone()))])],
						StateVersion::V1,
					);
					v.0
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

	/// Return the next key in storage (excluding this key) in lexicographic order or `None` if
	/// there is no value.
	fn next_storage_key(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		// TODO: query these in like groups of 1000 so we only need to go to the backend once
		// every 1000
		let binding = self.storage_keys_paged_remote(None, 1, Some(key)).unwrap();
		let next = binding.get(0).expect("count is 1, 0th index must exist. qed.");
		log::debug!(target: LOG_TARGET, "got next: {}", HexDisplay::from(&next.0.as_slice()));
		Ok(Some(next.0.clone()))
	}

	/// Return the next key in child storage in lexicographic order or `None` if there is no value.
	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		// TODO: query these in like groups of 1000 so we only need to go to the backend once
		// every 1000
		let binding = self.storage_child_keys_paged_remote(child_info, None, 1, Some(key)).unwrap();
		let key = binding.get(0).expect("count was 1, 0th index must exist. qed.");
		Ok(Some(key.0.clone()))
	}

	/// Calculate the storage root, with given delta over what is already stored in the backend, and
	/// produce a "transaction" that can be used to commit.
	///
	/// Does not include child storage updates.
	fn storage_root<'a>(
		&self,
		delta: impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>,
		state_version: StateVersion,
	) -> (<H as Hasher>::Out, Self::Transaction)
	where
		<H as Hasher>::Out: Ord + Decode + Encode,
	{
		self.cache.storage_root(delta, state_version)
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
	) -> (<H as Hasher>::Out, bool, Self::Transaction)
	where
		<H as Hasher>::Out: Ord,
	{
		self.cache.child_storage_root(child_info, delta, state_version)
	}

	// fn pairs<'a>(
	// 	&'a self,
	// 	_args: sp_state_machine::IterArgs,
	// ) -> Result<sp_state_machine::PairsIter<'a, H, Self::RawIter>, Self::Error> {
	// 	self.cache.pairs(args)
	// 	todo!()
	// }

	/// Get all keys with given prefix
	// fn keys<'a>(
	// 	&'a self,
	// 	args: sp_state_machine::IterArgs,
	// ) -> Result<sp_state_machine::KeysIter<'a, H, Self::RawIter>, Self::Error> {
	// 	let vec_args = args.into_iter().collect::<Vec<_>>();
	// 	let keys = self.keys_remote(args.collect());
	// 	todo!()
	// }

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
