// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

use std::{
	str::FromStr,
	sync::Arc,
	convert::TryFrom,
	thread::sleep,
	collections::HashSet,
};

use crate::NetworkProvider;
use futures::Future;
use log::error;
use sc_network::{PeerId, Multiaddr};
use codec::{Encode, Decode};
use sp_core::OpaquePeerId;
use sp_core::offchain::{
	Externalities as OffchainExt, HttpRequestId, Timestamp, HttpRequestStatus, HttpError,
	OffchainStorage, OpaqueNetworkState, OpaqueMultiaddr, StorageKind,
};
pub use sp_offchain::STORAGE_PREFIX;
pub use http::SharedClient;

#[cfg(not(target_os = "unknown"))]
mod http;

#[cfg(target_os = "unknown")]
use http_dummy as http;
#[cfg(target_os = "unknown")]
mod http_dummy;

mod timestamp;

/// Asynchronous offchain API.
///
/// NOTE this is done to prevent recursive calls into the runtime (which are not supported currently).
pub(crate) struct Api<Storage> {
	/// Offchain Workers database.
	db: Storage,
	/// A provider for substrate networking.
	network_provider: Arc<dyn NetworkProvider + Send + Sync>,
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

impl<Storage: OffchainStorage> OffchainExt for Api<Storage> {
	fn is_validator(&self) -> bool {
		self.is_validator
	}

	fn network_state(&self) -> Result<OpaqueNetworkState, ()> {
		let external_addresses = self.network_provider.external_addresses();

		let state = NetworkState::new(
			self.network_provider.local_peer_id(),
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

	fn local_storage_clear(&mut self, kind: StorageKind, key: &[u8]) {
		match kind {
			StorageKind::PERSISTENT => self.db.remove(STORAGE_PREFIX, key),
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

	fn set_authorized_nodes(&mut self, nodes: Vec<OpaquePeerId>, authorized_only: bool) {
		let peer_ids: HashSet<PeerId> = nodes.into_iter()
			.filter_map(|node| PeerId::from_bytes(&node.0).ok())
			.collect();

		self.network_provider.set_authorized_peers(peer_ids);
		self.network_provider.set_authorized_only(authorized_only);
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
		let enc = Encode::encode(&state.peer_id.to_bytes());
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
		let peer_id = PeerId::from_bytes(&bytes).map_err(|_| ())?;

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
pub(crate) struct AsyncApi {
	/// Everything HTTP-related is handled by a different struct.
	http: Option<http::HttpWorker>,
}

impl AsyncApi {
	/// Creates new Offchain extensions API implementation an the asynchronous processing part.
	pub fn new<S: OffchainStorage>(
		db: S,
		network_provider: Arc<dyn NetworkProvider + Send + Sync>,
		is_validator: bool,
		shared_client: SharedClient,
	) -> (Api<S>, Self) {
		let (http_api, http_worker) = http::http(shared_client);

		let api = Api {
			db,
			network_provider,
			is_validator,
			http: http_api,
		};

		let async_api = Self {
			http: Some(http_worker),
		};

		(api, async_api)
	}

	/// Run a processing task for the API
	pub fn process(mut self) -> impl Future<Output = ()> {
		let http = self.http.take().expect("Take invoked only once.");

		http
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::{convert::{TryFrom, TryInto}, time::SystemTime};
	use sc_client_db::offchain::LocalStorage;
	use sc_network::{NetworkStateInfo, PeerId};

	struct TestNetwork();

	impl NetworkProvider for TestNetwork {
		fn set_authorized_peers(&self, _peers: HashSet<PeerId>) {
			unimplemented!()
		}

		fn set_authorized_only(&self, _reserved_only: bool) {
			unimplemented!()
		}
	}

	impl NetworkStateInfo for TestNetwork {
		fn external_addresses(&self) -> Vec<Multiaddr> {
			Vec::new()
		}

		fn local_peer_id(&self) -> PeerId {
			PeerId::random()
		}
	}

	fn offchain_api() -> (Api<LocalStorage>, AsyncApi) {
		sp_tracing::try_init_simple();
		let db = LocalStorage::new_test();
		let mock = Arc::new(TestNetwork());
		let shared_client = SharedClient::new();

		AsyncApi::new(
			db,
			mock,
			false,
			shared_client,
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
		assert!(timestamp.unix_millis() >= d);
	}

	#[test]
	fn should_sleep() {
		let mut api = offchain_api().0;

		// Arrange.
		let now = api.timestamp();
		let delta = sp_core::offchain::Duration::from_millis(100);
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
