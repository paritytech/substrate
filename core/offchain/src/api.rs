// Copyright 2019 Parity Technologies (UK) Ltd.
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

use std::{
	str::FromStr,
	sync::Arc,
	convert::TryFrom,
	thread::sleep,
};

use client::backend::OffchainStorage;
use futures::{StreamExt as _, Future, FutureExt as _, future, channel::mpsc};
use log::{info, debug, warn, error};
use network::{PeerId, Multiaddr, NetworkStateInfo};
use codec::{Encode, Decode};
use primitives::offchain::{
	Externalities as OffchainExt, HttpRequestId, Timestamp, HttpRequestStatus, HttpError,
	OpaqueNetworkState, OpaquePeerId, OpaqueMultiaddr, StorageKind,
};
use sr_primitives::{generic::BlockId, traits::{self, Extrinsic}};
use transaction_pool::txpool::{Pool, ChainApi};

mod http;
mod timestamp;

/// A message between the offchain extension and the processing thread.
enum ExtMessage {
	SubmitExtrinsic(Vec<u8>),
}

/// Asynchronous offchain API.
///
/// NOTE this is done to prevent recursive calls into the runtime (which are not supported currently).
pub(crate) struct Api<Storage, Block: traits::Block> {
	sender: mpsc::UnboundedSender<ExtMessage>,
	db: Storage,
	network_state: Arc<dyn NetworkStateInfo + Send + Sync>,
	_at: BlockId<Block>,
	/// Is this node a potential validator?
	is_validator: bool,
	/// Everything HTTP-related is handled by a different struct.
	http: http::HttpApi,
}

fn unavailable_yet<R: Default>(name: &str) -> R {
	error!(
		"The {:?} API is not available for offchain workers yet. Follow \
		https://github.com/paritytech/substrate/issues/1458 for details", name
	);
	Default::default()
}

const LOCAL_DB: &str = "LOCAL (fork-aware) DB";
const STORAGE_PREFIX: &[u8] = b"storage";

impl<Storage, Block> OffchainExt for Api<Storage, Block>
where
	Storage: OffchainStorage,
	Block: traits::Block,
{
	fn is_validator(&self) -> bool {
		self.is_validator
	}

	fn submit_transaction(&mut self, ext: Vec<u8>) -> Result<(), ()> {
		self.sender
			.unbounded_send(ExtMessage::SubmitExtrinsic(ext))
			.map(|_| ())
			.map_err(|_| ())
	}

	fn network_state(&self) -> Result<OpaqueNetworkState, ()> {
		let external_addresses = self.network_state.external_addresses();

		let state = NetworkState::new(
			self.network_state.peer_id(),
			external_addresses,
		);
		Ok(OpaqueNetworkState::from(state))
	}

	fn timestamp(&mut self) -> Timestamp {
		timestamp::now()
	}

	fn sleep_until(&mut self, deadline: Timestamp) {
		sleep(timestamp::timestamp_from_now(deadline));
	}

	fn random_seed(&mut self) -> [u8; 32] {
		rand::random()
	}

	fn local_storage_set(&mut self, kind: StorageKind, key: &[u8], value: &[u8]) {
		match kind {
			StorageKind::PERSISTENT => self.db.set(STORAGE_PREFIX, key, value),
			StorageKind::LOCAL => unavailable_yet(LOCAL_DB),
		}
	}

	fn local_storage_compare_and_set(
		&mut self,
		kind: StorageKind,
		key: &[u8],
		old_value: Option<&[u8]>,
		new_value: &[u8],
	) -> bool {
		match kind {
			StorageKind::PERSISTENT => {
				self.db.compare_and_set(STORAGE_PREFIX, key, old_value, new_value)
			},
			StorageKind::LOCAL => unavailable_yet(LOCAL_DB),
		}
	}

	fn local_storage_get(&mut self, kind: StorageKind, key: &[u8]) -> Option<Vec<u8>> {
		match kind {
			StorageKind::PERSISTENT => self.db.get(STORAGE_PREFIX, key),
			StorageKind::LOCAL => unavailable_yet(LOCAL_DB),
		}
	}

	fn http_request_start(
		&mut self,
		method: &str,
		uri: &str,
		_meta: &[u8]
	) -> Result<HttpRequestId, ()> {
		self.http.request_start(method, uri)
	}

	fn http_request_add_header(
		&mut self,
		request_id: HttpRequestId,
		name: &str,
		value: &str
	) -> Result<(), ()> {
		self.http.request_add_header(request_id, name, value)
	}

	fn http_request_write_body(
		&mut self,
		request_id: HttpRequestId,
		chunk: &[u8],
		deadline: Option<Timestamp>
	) -> Result<(), HttpError> {
		self.http.request_write_body(request_id, chunk, deadline)
	}

	fn http_response_wait(
		&mut self,
		ids: &[HttpRequestId],
		deadline: Option<Timestamp>
	) -> Vec<HttpRequestStatus> {
		self.http.response_wait(ids, deadline)
	}

	fn http_response_headers(
		&mut self,
		request_id: HttpRequestId
	) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.http.response_headers(request_id)
	}

	fn http_response_read_body(
		&mut self,
		request_id: HttpRequestId,
		buffer: &mut [u8],
		deadline: Option<Timestamp>
	) -> Result<usize, HttpError> {
		self.http.response_read_body(request_id, buffer, deadline)
	}
}

/// Information about the local node's network state.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct NetworkState {
	peer_id: PeerId,
	external_addresses: Vec<Multiaddr>,
}

impl NetworkState {
	fn new(peer_id: PeerId, external_addresses: Vec<Multiaddr>) -> Self {
		NetworkState {
			peer_id,
			external_addresses,
		}
	}
}

impl From<NetworkState> for OpaqueNetworkState {
	fn from(state: NetworkState) -> OpaqueNetworkState {
		let enc = Encode::encode(&state.peer_id.into_bytes());
		let peer_id = OpaquePeerId::new(enc);

		let external_addresses: Vec<OpaqueMultiaddr> = state
			.external_addresses
			.iter()
			.map(|multiaddr| {
				let e = Encode::encode(&multiaddr.to_string());
				OpaqueMultiaddr::new(e)
			})
			.collect();

		OpaqueNetworkState {
			peer_id,
			external_addresses,
		}
	}
}

impl TryFrom<OpaqueNetworkState> for NetworkState {
	type Error = ();

	fn try_from(state: OpaqueNetworkState) -> Result<Self, Self::Error> {
		let inner_vec = state.peer_id.0;

		let bytes: Vec<u8> = Decode::decode(&mut &inner_vec[..]).map_err(|_| ())?;
		let peer_id = PeerId::from_bytes(bytes).map_err(|_| ())?;

		let external_addresses: Result<Vec<Multiaddr>, Self::Error> = state.external_addresses
			.iter()
			.map(|enc_multiaddr| -> Result<Multiaddr, Self::Error> {
				let inner_vec = &enc_multiaddr.0;
				let bytes = <Vec<u8>>::decode(&mut &inner_vec[..]).map_err(|_| ())?;
				let multiaddr_str = String::from_utf8(bytes).map_err(|_| ())?;
				let multiaddr = Multiaddr::from_str(&multiaddr_str).map_err(|_| ())?;
				Ok(multiaddr)
			})
			.collect();
		let external_addresses = external_addresses?;

		Ok(NetworkState {
			peer_id,
			external_addresses,
		})
	}
}

/// Offchain extensions implementation API
///
/// This is the asynchronous processing part of the API.
pub(crate) struct AsyncApi<A: ChainApi> {
	receiver: Option<mpsc::UnboundedReceiver<ExtMessage>>,
	transaction_pool: Arc<Pool<A>>,
	at: BlockId<A::Block>,
	/// Everything HTTP-related is handled by a different struct.
	http: Option<http::HttpWorker>,
}

impl<A: ChainApi> AsyncApi<A> {
	/// Creates new Offchain extensions API implementation  an the asynchronous processing part.
	pub fn new<S: OffchainStorage>(
		transaction_pool: Arc<Pool<A>>,
		db: S,
		at: BlockId<A::Block>,
		network_state: Arc<dyn NetworkStateInfo + Send + Sync>,
		is_validator: bool,
	) -> (Api<S, A::Block>, AsyncApi<A>) {
		let (sender, rx) = mpsc::unbounded();

		let (http_api, http_worker) = http::http();

		let api = Api {
			sender,
			db,
			network_state,
			_at: at,
			is_validator,
			http: http_api,
		};

		let async_api = AsyncApi {
			receiver: Some(rx),
			transaction_pool,
			at,
			http: Some(http_worker),
		};

		(api, async_api)
	}

	/// Run a processing task for the API
	pub fn process(mut self) -> impl Future<Output = ()> {
		let receiver = self.receiver.take().expect("Take invoked only once.");
		let http = self.http.take().expect("Take invoked only once.");

		let extrinsics = receiver.for_each(move |msg| {
			match msg {
				ExtMessage::SubmitExtrinsic(ext) => self.submit_extrinsic(ext),
			}
		});

		future::join(extrinsics, http)
			.map(|((), ())| ())
	}

	fn submit_extrinsic(&mut self, ext: Vec<u8>) -> impl Future<Output = ()> {
		let xt = match <A::Block as traits::Block>::Extrinsic::decode(&mut &*ext) {
			Ok(xt) => xt,
			Err(e) => {
				warn!("Unable to decode extrinsic: {:?}: {}", ext, e.what());
				return future::Either::Left(future::ready(()))
			},
		};

		info!("Submitting to the pool: {:?} (isSigned: {:?})", xt, xt.is_signed());
		future::Either::Right(self.transaction_pool
			.submit_one(&self.at, xt.clone())
			.map(|result| match result {
				Ok(hash) => { debug!("[{:?}] Offchain transaction added to the pool.", hash); },
				Err(e) => { debug!("Couldn't submit transaction: {:?}", e); },
			}))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::{convert::{TryFrom, TryInto}, time::SystemTime};
	use sr_primitives::traits::Zero;
	use client_db::offchain::LocalStorage;
	use network::PeerId;
	use test_client::runtime::Block;

	struct MockNetworkStateInfo();

	impl NetworkStateInfo for MockNetworkStateInfo {
		fn external_addresses(&self) -> Vec<Multiaddr> {
			Vec::new()
		}

		fn peer_id(&self) -> PeerId {
			PeerId::random()
		}
	}

	fn offchain_api() -> (Api<LocalStorage, Block>, AsyncApi<impl ChainApi>) {
		let _ = env_logger::try_init();
		let db = LocalStorage::new_test();
		let client = Arc::new(test_client::new());
		let pool = Arc::new(
			Pool::new(Default::default(), transaction_pool::FullChainApi::new(client.clone()))
		);

		let mock = Arc::new(MockNetworkStateInfo());
		AsyncApi::new(
			pool,
			db,
			BlockId::Number(Zero::zero()),
			mock,
			false,
		)
	}

	#[test]
	fn should_get_timestamp() {
		let mut api = offchain_api().0;

		// Get timestamp from std.
		let now = SystemTime::now();
		let d: u64 = now.duration_since(SystemTime::UNIX_EPOCH).unwrap().as_millis().try_into().unwrap();

		// Get timestamp from offchain api.
		let timestamp = api.timestamp();

		// Compare.
		assert!(timestamp.unix_millis() > 0);
		assert_eq!(timestamp.unix_millis(), d);
	}

	#[test]
	fn should_sleep() {
		let mut api = offchain_api().0;

		// Arrange.
		let now = api.timestamp();
		let delta = primitives::offchain::Duration::from_millis(100);
		let deadline = now.add(delta);

		// Act.
		api.sleep_until(deadline);
		let new_now = api.timestamp();

		// Assert.
		// The diff could be more than the sleep duration.
		assert!(new_now.unix_millis() - 100 >= now.unix_millis());
	}

	#[test]
	fn should_set_and_get_local_storage() {
		// given
		let kind = StorageKind::PERSISTENT;
		let mut api = offchain_api().0;
		let key = b"test";

		// when
		assert_eq!(api.local_storage_get(kind, key), None);
		api.local_storage_set(kind, key, b"value");

		// then
		assert_eq!(api.local_storage_get(kind, key), Some(b"value".to_vec()));
	}

	#[test]
	fn should_compare_and_set_local_storage() {
		// given
		let kind = StorageKind::PERSISTENT;
		let mut api = offchain_api().0;
		let key = b"test";
		api.local_storage_set(kind, key, b"value");

		// when
		assert_eq!(api.local_storage_compare_and_set(kind, key, Some(b"val"), b"xxx"), false);
		assert_eq!(api.local_storage_get(kind, key), Some(b"value".to_vec()));

		// when
		assert_eq!(api.local_storage_compare_and_set(kind, key, Some(b"value"), b"xxx"), true);
		assert_eq!(api.local_storage_get(kind, key), Some(b"xxx".to_vec()));
	}

	#[test]
	fn should_compare_and_set_local_storage_with_none() {
		// given
		let kind = StorageKind::PERSISTENT;
		let mut api = offchain_api().0;
		let key = b"test";

		// when
		let res = api.local_storage_compare_and_set(kind, key, None, b"value");

		// then
		assert_eq!(res, true);
		assert_eq!(api.local_storage_get(kind, key), Some(b"value".to_vec()));
	}

	#[test]
	fn should_convert_network_states() {
		// given
		let state = NetworkState::new(
			PeerId::random(),
			vec![
				Multiaddr::try_from("/ip4/127.0.0.1/tcp/1234".to_string()).unwrap(),
				Multiaddr::try_from("/ip6/2601:9:4f81:9700:803e:ca65:66e8:c21").unwrap(),
			],
		);

		// when
		let opaque_state = OpaqueNetworkState::from(state.clone());
		let converted_back_state = NetworkState::try_from(opaque_state).unwrap();

		// then
		assert_eq!(state, converted_back_state);
	}

	#[test]
	fn should_get_random_seed() {
		// given
		let mut api = offchain_api().0;
		let seed = api.random_seed();
		// then
		assert_ne!(seed, [0; 32]);
	}
}
