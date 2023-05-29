// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use std::{collections::HashSet, sync::Arc, thread::sleep};

use crate::NetworkProvider;
use codec::{Decode, Encode};
use futures::Future;
pub use http::SharedClient;
use libp2p::PeerId;
use sp_core::{
	offchain::{
		self, HttpError, HttpRequestId, HttpRequestStatus, OffchainStorage, OpaqueNetworkState,
		StorageKind, Timestamp,
	},
	OpaquePeerId,
};
pub use sp_offchain::STORAGE_PREFIX;

mod http;

mod timestamp;

fn unavailable_yet<R: Default>(name: &str) -> R {
	tracing::error!(
		target: super::LOG_TARGET,
		"The {:?} API is not available for offchain workers yet. Follow \
		https://github.com/paritytech/substrate/issues/1458 for details",
		name
	);
	Default::default()
}

const LOCAL_DB: &str = "LOCAL (fork-aware) DB";

/// Offchain DB reference.
#[derive(Debug, Clone)]
pub struct Db<Storage> {
	/// Persistent storage database.
	persistent: Storage,
}

impl<Storage: OffchainStorage> Db<Storage> {
	/// Create new instance of Offchain DB.
	pub fn new(persistent: Storage) -> Self {
		Self { persistent }
	}

	/// Create new instance of Offchain DB, backed by given backend.
	pub fn factory_from_backend<Backend, Block>(
		backend: &Backend,
	) -> Option<Box<dyn sc_client_api::execution_extensions::DbExternalitiesFactory>>
	where
		Backend: sc_client_api::Backend<Block, OffchainStorage = Storage>,
		Block: sp_runtime::traits::Block,
		Storage: 'static,
	{
		sc_client_api::Backend::offchain_storage(backend).map(|db| Box::new(Self::new(db)) as _)
	}
}

impl<Storage: OffchainStorage> offchain::DbExternalities for Db<Storage> {
	fn local_storage_set(&mut self, kind: StorageKind, key: &[u8], value: &[u8]) {
		tracing::debug!(
			target: "offchain-worker::storage",
			?kind,
			key = ?array_bytes::bytes2hex("", key),
			value = ?array_bytes::bytes2hex("", value),
			"Write",
		);
		match kind {
			StorageKind::PERSISTENT => self.persistent.set(STORAGE_PREFIX, key, value),
			StorageKind::LOCAL => unavailable_yet(LOCAL_DB),
		}
	}

	fn local_storage_clear(&mut self, kind: StorageKind, key: &[u8]) {
		tracing::debug!(
			target: "offchain-worker::storage",
			?kind,
			key = ?array_bytes::bytes2hex("", key),
			"Clear",
		);
		match kind {
			StorageKind::PERSISTENT => self.persistent.remove(STORAGE_PREFIX, key),
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
		tracing::debug!(
			target: "offchain-worker::storage",
			?kind,
			key = ?array_bytes::bytes2hex("", key),
			new_value = ?array_bytes::bytes2hex("", new_value),
			old_value = ?old_value.as_ref().map(|s| array_bytes::bytes2hex("", s)),
			"CAS",
		);
		match kind {
			StorageKind::PERSISTENT =>
				self.persistent.compare_and_set(STORAGE_PREFIX, key, old_value, new_value),
			StorageKind::LOCAL => unavailable_yet(LOCAL_DB),
		}
	}

	fn local_storage_get(&mut self, kind: StorageKind, key: &[u8]) -> Option<Vec<u8>> {
		let result = match kind {
			StorageKind::PERSISTENT => self.persistent.get(STORAGE_PREFIX, key),
			StorageKind::LOCAL => unavailable_yet(LOCAL_DB),
		};
		tracing::debug!(
			target: "offchain-worker::storage",
			?kind,
			key = ?array_bytes::bytes2hex("", key),
			result = ?result.as_ref().map(|s| array_bytes::bytes2hex("", s)),
			"Read",
		);
		result
	}
}

/// Asynchronous offchain API.
///
/// NOTE this is done to prevent recursive calls into the runtime
/// (which are not supported currently).
pub(crate) struct Api {
	/// A provider for substrate networking.
	network_provider: Arc<dyn NetworkProvider + Send + Sync>,
	/// Is this node a potential validator?
	is_validator: bool,
	/// Everything HTTP-related is handled by a different struct.
	http: http::HttpApi,
}

impl offchain::Externalities for Api {
	fn is_validator(&self) -> bool {
		self.is_validator
	}

	fn network_state(&self) -> Result<OpaqueNetworkState, ()> {
		let state = NetworkState::new(self.network_provider.local_peer_id());
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

	fn http_request_start(
		&mut self,
		method: &str,
		uri: &str,
		_meta: &[u8],
	) -> Result<HttpRequestId, ()> {
		self.http.request_start(method, uri)
	}

	fn http_request_add_header(
		&mut self,
		request_id: HttpRequestId,
		name: &str,
		value: &str,
	) -> Result<(), ()> {
		self.http.request_add_header(request_id, name, value)
	}

	fn http_request_write_body(
		&mut self,
		request_id: HttpRequestId,
		chunk: &[u8],
		deadline: Option<Timestamp>,
	) -> Result<(), HttpError> {
		self.http.request_write_body(request_id, chunk, deadline)
	}

	fn http_response_wait(
		&mut self,
		ids: &[HttpRequestId],
		deadline: Option<Timestamp>,
	) -> Vec<HttpRequestStatus> {
		self.http.response_wait(ids, deadline)
	}

	fn http_response_headers(&mut self, request_id: HttpRequestId) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.http.response_headers(request_id)
	}

	fn http_response_read_body(
		&mut self,
		request_id: HttpRequestId,
		buffer: &mut [u8],
		deadline: Option<Timestamp>,
	) -> Result<usize, HttpError> {
		self.http.response_read_body(request_id, buffer, deadline)
	}

	fn set_authorized_nodes(&mut self, nodes: Vec<OpaquePeerId>, authorized_only: bool) {
		let peer_ids: HashSet<PeerId> =
			nodes.into_iter().filter_map(|node| PeerId::from_bytes(&node.0).ok()).collect();

		self.network_provider.set_authorized_peers(peer_ids);
		self.network_provider.set_authorized_only(authorized_only);
	}
}

/// Information about the local node's network state.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct NetworkState {
	peer_id: PeerId,
}

impl NetworkState {
	fn new(peer_id: PeerId) -> Self {
		NetworkState { peer_id }
	}
}

impl From<NetworkState> for OpaqueNetworkState {
	fn from(state: NetworkState) -> OpaqueNetworkState {
		let enc = Encode::encode(&state.peer_id.to_bytes());
		let peer_id = OpaquePeerId::new(enc);

		OpaqueNetworkState { peer_id }
	}
}

impl TryFrom<OpaqueNetworkState> for NetworkState {
	type Error = ();

	fn try_from(state: OpaqueNetworkState) -> Result<Self, Self::Error> {
		let inner_vec = state.peer_id.0;

		let bytes: Vec<u8> = Decode::decode(&mut &inner_vec[..]).map_err(|_| ())?;
		let peer_id = PeerId::from_bytes(&bytes).map_err(|_| ())?;

		Ok(NetworkState { peer_id })
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
	/// Creates new Offchain extensions API implementation and the asynchronous processing part.
	pub fn new(
		network_provider: Arc<dyn NetworkProvider + Send + Sync>,
		is_validator: bool,
		shared_http_client: SharedClient,
	) -> (Api, Self) {
		let (http_api, http_worker) = http::http(shared_http_client);

		let api = Api { network_provider, is_validator, http: http_api };

		let async_api = Self { http: Some(http_worker) };

		(api, async_api)
	}

	/// Run a processing task for the API
	pub fn process(self) -> impl Future<Output = ()> {
		self.http.expect("`process` is only called once; qed")
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use libp2p::PeerId;
	use sc_client_db::offchain::LocalStorage;
	use sc_network::{
		config::MultiaddrWithPeerId, types::ProtocolName, NetworkPeers, NetworkStateInfo,
	};
	use sc_peerset::ReputationChange;
	use sp_core::offchain::{DbExternalities, Externalities};
	use std::time::SystemTime;

	pub(super) struct TestNetwork();

	impl NetworkPeers for TestNetwork {
		fn set_authorized_peers(&self, _peers: HashSet<PeerId>) {
			unimplemented!();
		}

		fn set_authorized_only(&self, _reserved_only: bool) {
			unimplemented!();
		}

		fn add_known_address(&self, _peer_id: PeerId, _addr: Multiaddr) {
			unimplemented!();
		}

		fn report_peer(&self, _who: PeerId, _cost_benefit: ReputationChange) {
			unimplemented!();
		}

		fn disconnect_peer(&self, _who: PeerId, _protocol: ProtocolName) {
			unimplemented!();
		}

		fn accept_unreserved_peers(&self) {
			unimplemented!();
		}

		fn deny_unreserved_peers(&self) {
			unimplemented!();
		}

		fn add_reserved_peer(&self, _peer: MultiaddrWithPeerId) -> Result<(), String> {
			unimplemented!();
		}

		fn remove_reserved_peer(&self, _peer_id: PeerId) {
			unimplemented!();
		}

		fn set_reserved_peers(
			&self,
			_protocol: ProtocolName,
			_peers: HashSet<Multiaddr>,
		) -> Result<(), String> {
			unimplemented!();
		}

		fn add_peers_to_reserved_set(
			&self,
			_protocol: ProtocolName,
			_peers: HashSet<Multiaddr>,
		) -> Result<(), String> {
			unimplemented!();
		}

		fn remove_peers_from_reserved_set(&self, _protocol: ProtocolName, _peers: Vec<PeerId>) {
			unimplemented!();
		}

		fn add_to_peers_set(
			&self,
			_protocol: ProtocolName,
			_peers: HashSet<Multiaddr>,
		) -> Result<(), String> {
			unimplemented!();
		}

		fn remove_from_peers_set(&self, _protocol: ProtocolName, _peers: Vec<PeerId>) {
			unimplemented!();
		}

		fn sync_num_connected(&self) -> usize {
			unimplemented!();
		}
	}

	impl NetworkStateInfo for TestNetwork {
		fn local_peer_id(&self) -> PeerId {
			PeerId::random()
		}

		fn listen_addresses(&self) -> Vec<Multiaddr> {
			Vec::new()
		}
	}

	fn offchain_api() -> (Api, AsyncApi) {
		sp_tracing::try_init_simple();
		let mock = Arc::new(TestNetwork());
		let shared_client = SharedClient::new();

		AsyncApi::new(mock, false, shared_client)
	}

	fn offchain_db() -> Db<LocalStorage> {
		Db::new(LocalStorage::new_test())
	}

	#[test]
	fn should_get_timestamp() {
		let mut api = offchain_api().0;

		// Get timestamp from std.
		let now = SystemTime::now();
		let d: u64 = now
			.duration_since(SystemTime::UNIX_EPOCH)
			.unwrap()
			.as_millis()
			.try_into()
			.unwrap();

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
		let mut api = offchain_db();
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
		let mut api = offchain_db();
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
		let mut api = offchain_db();
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
		let state = NetworkState::new(PeerId::random());

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
