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

#![warn(missing_docs)]

//! Substrate authority discovery.
//!
//! This crate enables Substrate authorities to directly connect to other authorities. [`AuthorityDiscovery`] implements
//! the Future trait. By polling [`AuthorityDiscovery`] an authority:
//!
//!
//! 1. **Makes itself discoverable**
//!
//!    1. Retrieves its external addresses.
//!
//!    2. Adds its network peer id to the addresses.
//!
//!    3. Signs the above.
//!
//!    4. Puts the signature and the addresses on the libp2p Kademlia DHT.
//!
//!
//! 2. **Discovers other authorities**
//!
//!    1. Retrieves the current set of authorities.
//!
//!    2. Starts DHT queries for the ids of the authorities.
//!
//!    3. Validates the signatures of the retrieved key value pairs.
//!
//!    4. Adds the retrieved external addresses as priority nodes to the peerset.
use std::collections::{HashMap, HashSet};
use std::convert::TryInto;
use std::iter::FromIterator;
use std::marker::PhantomData;
use std::pin::Pin;
use std::sync::Arc;
use std::time::Duration;

use futures::channel::mpsc::Receiver;
use futures::stream::StreamExt;
use futures::task::{Context, Poll};
use futures::Future;
use futures_timer::Interval;

use authority_discovery_primitives::{AuthorityDiscoveryApi, AuthorityId, Signature};
use client::blockchain::HeaderBackend;
use error::{Error, Result};
use log::{debug, error, log_enabled, warn};
use network::specialization::NetworkSpecialization;
use network::{DhtEvent, ExHashT};
use prost::Message;
use sr_primitives::generic::BlockId;
use sr_primitives::traits::{Block as BlockT, ProvideRuntimeApi};

mod error;
/// Dht payload schemas generated from Protobuf definitions via Prost crate in build.rs.
mod schema {
	include!(concat!(env!("OUT_DIR"), "/authority_discovery.rs"));
}

/// An `AuthorityDiscovery` makes a given authority discoverable and discovers other authorities.
pub struct AuthorityDiscovery<Client, Network, Block>
where
	Block: BlockT + 'static,
	Network: NetworkProvider,
	Client: ProvideRuntimeApi + Send + Sync + 'static + HeaderBackend<Block>,
	<Client as ProvideRuntimeApi>::Api: AuthorityDiscoveryApi<Block>,
{
	client: Arc<Client>,

	network: Arc<Network>,
	/// Channel we receive Dht events on.
	dht_event_rx: Receiver<DhtEvent>,

	/// Interval to be proactive, publishing own addresses.
	publish_interval: Interval,
	/// Interval on which to query for addresses of other authorities.
	query_interval: Interval,

	/// The network peerset interface for priority groups lets us only set an entire group, but we retrieve the
	/// addresses of other authorities one by one from the network. To use the peerset interface we need to cache the
	/// addresses and always overwrite the entire peerset priority group. To ensure this map doesn't grow indefinitely
	/// `purge_old_authorities_from_cache` function is called each time we add a new entry.
	address_cache: HashMap<AuthorityId, Vec<libp2p::Multiaddr>>,

	phantom: PhantomData<Block>,
}

impl<Client, Network, Block> AuthorityDiscovery<Client, Network, Block>
where
	Block: BlockT + Unpin + 'static,
	Network: NetworkProvider,
	Client: ProvideRuntimeApi + Send + Sync + 'static + HeaderBackend<Block>,
	<Client as ProvideRuntimeApi>::Api: AuthorityDiscoveryApi<Block>,
	Self: Future<Output = ()>,
{
	/// Return a new authority discovery.
	pub fn new(
		client: Arc<Client>,
		network: Arc<Network>,
		dht_event_rx: Receiver<DhtEvent>,
	) -> Self {
		// Kademlia's default time-to-live for Dht records is 36h, republishing records every 24h. Given that a node
		// could restart at any point in time, one can not depend on the republishing process, thus publishing own
		// external addresses should happen on an interval < 36h.
		let publish_interval = Interval::new(Duration::from_secs(12 * 60 * 60));

		// External addresses of other authorities can change at any given point in time. The interval on which to query
		// for external addresses of other authorities is a trade off between efficiency and performance.
		let query_interval = Interval::new(Duration::from_secs(10 * 60));

		let address_cache = HashMap::new();

		AuthorityDiscovery {
			client,
			network,
			dht_event_rx,
			publish_interval,
			query_interval,
			address_cache,
			phantom: PhantomData,
		}
	}

	fn publish_own_ext_addresses(&mut self) -> Result<()> {
		let id = BlockId::hash(self.client.info().best_hash);

		let addresses = self
			.network
			.external_addresses()
			.into_iter()
			.map(|a| {
				a.with(libp2p::core::multiaddr::Protocol::P2p(
					self.network.local_peer_id().into(),
				))
			})
			.map(|a| a.to_vec())
			.collect();

		let mut serialized_addresses = vec![];
		schema::AuthorityAddresses { addresses }
			.encode(&mut serialized_addresses)
			.map_err(Error::Encoding)?;

		let (signature, authority_id) = self
			.client
			.runtime_api()
			.sign(&id, &serialized_addresses)
			.map_err(Error::CallingRuntime)?
			.ok_or(Error::SigningDhtPayload)?;

		let mut signed_addresses = vec![];
		schema::SignedAuthorityAddresses {
			addresses: serialized_addresses,
			signature: signature.0,
		}
		.encode(&mut signed_addresses)
		.map_err(Error::Encoding)?;

		self.network.put_value(
			hash_authority_id(authority_id.0.as_ref())?,
			signed_addresses,
		);

		Ok(())
	}

	fn request_addresses_of_others(&mut self) -> Result<()> {
		let id = BlockId::hash(self.client.info().best_hash);

		let authorities = self
			.client
			.runtime_api()
			.authorities(&id)
			.map_err(Error::CallingRuntime)?;

		for authority_id in authorities.iter() {
			self.network
				.get_value(&hash_authority_id(authority_id.0.as_ref())?);
		}

		Ok(())
	}

	fn handle_dht_events(&mut self, cx: &mut Context) -> Result<()> {
		while let Poll::Ready(Some(event)) = self.dht_event_rx.poll_next_unpin(cx) {
			match event {
				DhtEvent::ValueFound(v) => {
					if log_enabled!(log::Level::Debug) {
						let hashes = v.iter().map(|(hash, _value)| hash.clone());
						debug!(target: "sub-authority-discovery", "Value for hash '{:?}' found on Dht.", hashes);
					}

					self.handle_dht_value_found_event(v)?;
				}
				DhtEvent::ValueNotFound(hash) => warn!(
					target: "sub-authority-discovery",
					"Value for hash '{:?}' not found on Dht.", hash
				),
				DhtEvent::ValuePut(hash) => debug!(
					target: "sub-authority-discovery",
					"Successfully put hash '{:?}' on Dht.", hash),
				DhtEvent::ValuePutFailed(hash) => warn!(
					target: "sub-authority-discovery",
					"Failed to put hash '{:?}' on Dht.", hash
				),
			}
		}

		Ok(())
	}

	fn handle_dht_value_found_event(
		&mut self,
		values: Vec<(libp2p::kad::record::Key, Vec<u8>)>,
	) -> Result<()> {
		debug!(target: "sub-authority-discovery", "Got Dht value from network.");

		let id = BlockId::hash(self.client.info().best_hash);

		// From the Dht we only get the hashed authority id. In order to retrieve the actual authority id and to ensure
		// it is actually an authority, we match the hash against the hash of the authority id of all other authorities.
		let authorities = self.client.runtime_api().authorities(&id)?;
		self.purge_old_authorities_from_cache(&authorities);

		let authorities = authorities
			.into_iter()
			.map(|a| hash_authority_id(a.0.as_ref()).map(|h| (h, a)))
			.collect::<Result<HashMap<_, _>>>()?;

		for (key, value) in values.iter() {
			// Check if the event origins from an authority in the current authority set.
			let authority_id: &AuthorityId = authorities
				.get(key)
				.ok_or(Error::MatchingHashedAuthorityIdWithAuthorityId)?;

			let schema::SignedAuthorityAddresses {
				signature,
				addresses,
			} = schema::SignedAuthorityAddresses::decode(value).map_err(Error::Decoding)?;
			let signature = Signature(signature);

			let is_verified = self
				.client
				.runtime_api()
				.verify(&id, &addresses, &signature, &authority_id.clone())
				.map_err(Error::CallingRuntime)?;

			if !is_verified {
				return Err(Error::VerifyingDhtPayload);
			}

			let addresses: Vec<libp2p::Multiaddr> = schema::AuthorityAddresses::decode(addresses)
				.map(|a| a.addresses)
				.map_err(Error::Decoding)?
				.into_iter()
				.map(|a| a.try_into())
				.collect::<std::result::Result<_, _>>()
				.map_err(Error::ParsingMultiaddress)?;

			self.address_cache.insert(authority_id.clone(), addresses);
		}

		// Let's update the peerset priority group with the all the addresses we have in our cache.

		let addresses = HashSet::from_iter(
			self.address_cache
				.iter()
				.map(|(_peer_id, addresses)| addresses.clone())
				.flatten(),
		);

		debug!(target: "sub-authority-discovery", "Applying priority group {:#?} to peerset.", addresses);
		self.network
			.set_priority_group("authorities".to_string(), addresses)
			.map_err(Error::SettingPeersetPriorityGroup)?;

		Ok(())
	}

	fn purge_old_authorities_from_cache(&mut self, current_authorities: &Vec<AuthorityId>) {
		self.address_cache
			.retain(|peer_id, _addresses| current_authorities.contains(peer_id))
	}
}

impl<Client, Network, Block> Future for AuthorityDiscovery<Client, Network, Block>
where
	Block: BlockT + Unpin + 'static,
	Network: NetworkProvider,
	Client: ProvideRuntimeApi + Send + Sync + 'static + HeaderBackend<Block>,
	<Client as ProvideRuntimeApi>::Api: AuthorityDiscoveryApi<Block>,
{
	type Output = ();

	fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		let mut inner = || -> Result<()> {
			// Process incoming events before triggering new ones.
			self.handle_dht_events(cx)?;

			if let Poll::Ready(_) = self.publish_interval.poll_next_unpin(cx) {
				// Make sure to call interval.poll until it returns Async::NotReady once. Otherwise, in case one of the
				// function calls within this block do a `return`, we don't call `interval.poll` again and thereby the
				// underlying Tokio task is never registered with Tokio's Reactor to be woken up on the next interval
				// tick.
				while let Poll::Ready(_) = self.publish_interval.poll_next_unpin(cx) {}

				self.publish_own_ext_addresses()?;
			}

			if let Poll::Ready(_) = self.query_interval.poll_next_unpin(cx) {
				// Make sure to call interval.poll until it returns Async::NotReady once. Otherwise, in case one of the
				// function calls within this block do a `return`, we don't call `interval.poll` again and thereby the
				// underlying Tokio task is never registered with Tokio's Reactor to be woken up on the next interval
				// tick.
				while let Poll::Ready(_) = self.query_interval.poll_next_unpin(cx) {}

				self.request_addresses_of_others()?;
			}

			Ok(())
		};

		match inner() {
			Ok(()) => {}
			Err(e) => error!(target: "sub-authority-discovery", "Poll failure: {:?}", e),
		};

		// Make sure to always return NotReady as this is a long running task with the same lifetime as the node itself.
		Poll::Pending
	}
}

/// NetworkProvider provides AuthorityDiscovery with all necessary hooks into the underlying Substrate networking. Using
/// this trait abstraction instead of NetworkService directly is necessary to unit test AuthorityDiscovery.
pub trait NetworkProvider {
	/// Returns the local external addresses.
	fn external_addresses(&self) -> Vec<libp2p::Multiaddr>;

	/// Returns the network identity of the node.
	fn local_peer_id(&self) -> libp2p::PeerId;

	/// Modify a peerset priority group.
	fn set_priority_group(
		&self,
		group_id: String,
		peers: HashSet<libp2p::Multiaddr>,
	) -> std::result::Result<(), String>;

	/// Start putting a value in the Dht.
	fn put_value(&self, key: libp2p::kad::record::Key, value: Vec<u8>);

	/// Start getting a value from the Dht.
	fn get_value(&self, key: &libp2p::kad::record::Key);
}

impl<B, S, H> NetworkProvider for network::NetworkService<B, S, H>
where
	B: BlockT + 'static,
	S: NetworkSpecialization<B>,
	H: ExHashT,
{
	fn external_addresses(&self) -> Vec<libp2p::Multiaddr> {
		self.external_addresses()
	}
	fn local_peer_id(&self) -> libp2p::PeerId {
		self.local_peer_id()
	}
	fn set_priority_group(
		&self,
		group_id: String,
		peers: HashSet<libp2p::Multiaddr>,
	) -> std::result::Result<(), String> {
		self.set_priority_group(group_id, peers)
	}
	fn put_value(&self, key: libp2p::kad::record::Key, value: Vec<u8>) {
		self.put_value(key, value)
	}
	fn get_value(&self, key: &libp2p::kad::record::Key) {
		self.get_value(key)
	}
}

fn hash_authority_id(id: &[u8]) -> Result<libp2p::kad::record::Key> {
	libp2p::multihash::encode(libp2p::multihash::Hash::SHA2256, id)
		.map(|k| libp2p::kad::record::Key::new(&k))
		.map_err(Error::HashingAuthorityId)
}

#[cfg(test)]
mod tests {
	use super::*;
	use client::runtime_api::{ApiExt, Core, RuntimeVersion, StorageProof};
	use futures::channel::mpsc::channel;
	use futures::executor::block_on;
	use futures::future::poll_fn;
	use primitives::{ExecutionContext, NativeOrEncoded};
	use sr_primitives::traits::Zero;
	use sr_primitives::traits::{ApiRef, Block as BlockT, NumberFor, ProvideRuntimeApi};
	use std::sync::{Arc, Mutex};
	use test_client::runtime::Block;

	#[derive(Clone)]
	struct TestApi {}

	impl ProvideRuntimeApi for TestApi {
		type Api = RuntimeApi;

		fn runtime_api<'a>(&'a self) -> ApiRef<'a, Self::Api> {
			RuntimeApi {}.into()
		}
	}

	/// Blockchain database header backend. Does not perform any validation.
	impl<Block: BlockT> HeaderBackend<Block> for TestApi {
		fn header(
			&self,
			_id: BlockId<Block>,
		) -> std::result::Result<Option<Block::Header>, client::error::Error> {
			Ok(None)
		}

		fn info(&self) -> client::blockchain::Info<Block> {
			client::blockchain::Info {
				best_hash: Default::default(),
				best_number: Zero::zero(),
				finalized_hash: Default::default(),
				finalized_number: Zero::zero(),
				genesis_hash: Default::default(),
			}
		}

		fn status(
			&self,
			_id: BlockId<Block>,
		) -> std::result::Result<client::blockchain::BlockStatus, client::error::Error> {
			Ok(client::blockchain::BlockStatus::Unknown)
		}

		fn number(
			&self,
			_hash: Block::Hash,
		) -> std::result::Result<Option<NumberFor<Block>>, client::error::Error> {
			Ok(None)
		}

		fn hash(
			&self,
			_number: NumberFor<Block>,
		) -> std::result::Result<Option<Block::Hash>, client::error::Error> {
			Ok(None)
		}
	}

	struct RuntimeApi {}

	impl Core<Block> for RuntimeApi {
		fn Core_version_runtime_api_impl(
			&self,
			_: &BlockId<Block>,
			_: ExecutionContext,
			_: Option<()>,
			_: Vec<u8>,
		) -> std::result::Result<NativeOrEncoded<RuntimeVersion>, client::error::Error> {
			unimplemented!("Not required for testing!")
		}

		fn Core_execute_block_runtime_api_impl(
			&self,
			_: &BlockId<Block>,
			_: ExecutionContext,
			_: Option<(Block)>,
			_: Vec<u8>,
		) -> std::result::Result<NativeOrEncoded<()>, client::error::Error> {
			unimplemented!("Not required for testing!")
		}

		fn Core_initialize_block_runtime_api_impl(
			&self,
			_: &BlockId<Block>,
			_: ExecutionContext,
			_: Option<&<Block as BlockT>::Header>,
			_: Vec<u8>,
		) -> std::result::Result<NativeOrEncoded<()>, client::error::Error> {
			unimplemented!("Not required for testing!")
		}
	}

	impl ApiExt<Block> for RuntimeApi {
		fn map_api_result<F: FnOnce(&Self) -> std::result::Result<R, E>, R, E>(
			&self,
			_: F,
		) -> std::result::Result<R, E> {
			unimplemented!("Not required for testing!")
		}

		fn runtime_version_at(
			&self,
			_: &BlockId<Block>,
		) -> std::result::Result<RuntimeVersion, client::error::Error> {
			unimplemented!("Not required for testing!")
		}

		fn record_proof(&mut self) {
			unimplemented!("Not required for testing!")
		}

		fn extract_proof(&mut self) -> Option<StorageProof> {
			unimplemented!("Not required for testing!")
		}
	}

	impl AuthorityDiscoveryApi<Block> for RuntimeApi {
		fn AuthorityDiscoveryApi_authorities_runtime_api_impl(
			&self,
			_: &BlockId<Block>,
			_: ExecutionContext,
			_: Option<()>,
			_: Vec<u8>,
		) -> std::result::Result<NativeOrEncoded<Vec<AuthorityId>>, client::error::Error> {
			return Ok(NativeOrEncoded::Native(vec![
				AuthorityId("test-authority-id-1".as_bytes().to_vec()),
				AuthorityId("test-authority-id-2".as_bytes().to_vec()),
			]));
		}
		fn AuthorityDiscoveryApi_sign_runtime_api_impl(
			&self,
			_: &BlockId<Block>,
			_: ExecutionContext,
			_: Option<&std::vec::Vec<u8>>,
			_: Vec<u8>,
		) -> std::result::Result<
			NativeOrEncoded<Option<(Signature, AuthorityId)>>,
			client::error::Error,
		> {
			return Ok(NativeOrEncoded::Native(Some((
				Signature("test-signature-1".as_bytes().to_vec()),
				AuthorityId("test-authority-id-1".as_bytes().to_vec()),
			))));
		}
		fn AuthorityDiscoveryApi_verify_runtime_api_impl(
			&self,
			_: &BlockId<Block>,
			_: ExecutionContext,
			args: Option<(&Vec<u8>, &Signature, &AuthorityId)>,
			_: Vec<u8>,
		) -> std::result::Result<NativeOrEncoded<bool>, client::error::Error> {
			if *args.unwrap().1 == Signature("test-signature-1".as_bytes().to_vec()) {
				return Ok(NativeOrEncoded::Native(true));
			}
			return Ok(NativeOrEncoded::Native(false));
		}
	}

	#[derive(Default)]
	struct TestNetwork {
		// Whenever functions on `TestNetwork` are called, the function arguments are added to the vectors below.
		pub put_value_call: Arc<Mutex<Vec<(libp2p::kad::record::Key, Vec<u8>)>>>,
		pub get_value_call: Arc<Mutex<Vec<libp2p::kad::record::Key>>>,
		pub set_priority_group_call: Arc<Mutex<Vec<(String, HashSet<libp2p::Multiaddr>)>>>,
	}

	impl NetworkProvider for TestNetwork {
		fn external_addresses(&self) -> Vec<libp2p::Multiaddr> {
			vec![]
		}
		fn local_peer_id(&self) -> libp2p::PeerId {
			libp2p::PeerId::random()
		}
		fn set_priority_group(
			&self,
			group_id: String,
			peers: HashSet<libp2p::Multiaddr>,
		) -> std::result::Result<(), String> {
			self.set_priority_group_call
				.lock()
				.unwrap()
				.push((group_id, peers));
			Ok(())
		}
		fn put_value(&self, key: libp2p::kad::record::Key, value: Vec<u8>) {
			self.put_value_call.lock().unwrap().push((key, value));
		}
		fn get_value(&self, key: &libp2p::kad::record::Key) {
			self.get_value_call.lock().unwrap().push(key.clone());
		}
	}

	#[test]
	fn publish_own_ext_addresses_puts_record_on_dht() {
		let (_dht_event_tx, dht_event_rx) = channel(1000);
		let test_api = Arc::new(TestApi {});
		let network: Arc<TestNetwork> = Arc::new(Default::default());

		let mut authority_discovery =
			AuthorityDiscovery::new(test_api, network.clone(), dht_event_rx);

		authority_discovery.publish_own_ext_addresses().unwrap();

		// Expect authority discovery to put a new record onto the dht.
		assert_eq!(network.put_value_call.lock().unwrap().len(), 1);
	}

	#[test]
	fn request_addresses_of_others_triggers_dht_get_query() {
		let (_dht_event_tx, dht_event_rx) = channel(1000);
		let test_api = Arc::new(TestApi {});
		let network: Arc<TestNetwork> = Arc::new(Default::default());

		let mut authority_discovery =
			AuthorityDiscovery::new(test_api, network.clone(), dht_event_rx);

		authority_discovery.request_addresses_of_others().unwrap();

		// Expect authority discovery to request new records from the dht.
		assert_eq!(network.get_value_call.lock().unwrap().len(), 2);
	}

	#[test]
	fn handle_dht_events_with_value_found_should_call_set_priority_group() {
		// Create authority discovery.

		let (mut dht_event_tx, dht_event_rx) = channel(1000);
		let test_api = Arc::new(TestApi {});
		let network: Arc<TestNetwork> = Arc::new(Default::default());

		let mut authority_discovery =
			AuthorityDiscovery::new(test_api, network.clone(), dht_event_rx);

		// Create sample dht event.

		let authority_id_1 = hash_authority_id("test-authority-id-1".as_bytes()).unwrap();
		let address_1: libp2p::Multiaddr = "/ip6/2001:db8::".parse().unwrap();

		let mut serialized_addresses = vec![];
		schema::AuthorityAddresses {
			addresses: vec![address_1.to_vec()],
		}
		.encode(&mut serialized_addresses)
		.unwrap();

		let mut signed_addresses = vec![];
		schema::SignedAuthorityAddresses {
			addresses: serialized_addresses,
			signature: "test-signature-1".as_bytes().to_vec(),
		}
		.encode(&mut signed_addresses)
		.unwrap();

		let dht_event = network::DhtEvent::ValueFound(vec![(authority_id_1, signed_addresses)]);
		dht_event_tx.try_send(dht_event).unwrap();

		// Make authority discovery handle the event.
		let f = |cx: &mut Context<'_>| -> Poll<()> {
			authority_discovery.handle_dht_events(cx).unwrap();

			// Expect authority discovery to set the priority set.
			assert_eq!(network.set_priority_group_call.lock().unwrap().len(), 1);

			assert_eq!(
				network.set_priority_group_call.lock().unwrap()[0],
				(
					"authorities".to_string(),
					HashSet::from_iter(vec![address_1.clone()].into_iter())
				)
			);

			Poll::Ready(())
		};

		let _ = block_on(poll_fn(f));
	}
}
