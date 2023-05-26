// This file is part of Substrate.
//
// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.
//
// If you read this, you are very thorough, congratulations.

use crate::{
	config::MultiaddrWithPeerId,
	event::Event,
	request_responses::{IfDisconnected, RequestFailure},
	service::signature::Signature,
	types::ProtocolName,
};

use futures::{channel::oneshot, Stream};
use libp2p::{Multiaddr, PeerId};

use sc_peerset::ReputationChange;

use std::{collections::HashSet, future::Future, pin::Pin, sync::Arc};

pub use libp2p::{identity::SigningError, kad::record::Key as KademliaKey};

/// Signer with network identity
pub trait NetworkSigner {
	/// Signs the message with the `KeyPair` that defines the local [`PeerId`].
	fn sign_with_local_identity(&self, msg: impl AsRef<[u8]>) -> Result<Signature, SigningError>;
}

impl<T> NetworkSigner for Arc<T>
where
	T: ?Sized,
	T: NetworkSigner,
{
	fn sign_with_local_identity(&self, msg: impl AsRef<[u8]>) -> Result<Signature, SigningError> {
		T::sign_with_local_identity(self, msg)
	}
}

/// Provides access to the networking DHT.
pub trait NetworkDHTProvider {
	/// Start getting a value from the DHT.
	fn get_value(&self, key: &KademliaKey);

	/// Start putting a value in the DHT.
	fn put_value(&self, key: KademliaKey, value: Vec<u8>);
}

impl<T> NetworkDHTProvider for Arc<T>
where
	T: ?Sized,
	T: NetworkDHTProvider,
{
	fn get_value(&self, key: &KademliaKey) {
		T::get_value(self, key)
	}

	fn put_value(&self, key: KademliaKey, value: Vec<u8>) {
		T::put_value(self, key, value)
	}
}

/// Provides an ability to set a fork sync request for a particular block.
pub trait NetworkSyncForkRequest<BlockHash, BlockNumber> {
	/// Notifies the sync service to try and sync the given block from the given
	/// peers.
	///
	/// If the given vector of peers is empty then the underlying implementation
	/// should make a best effort to fetch the block from any peers it is
	/// connected to (NOTE: this assumption will change in the future #3629).
	fn set_sync_fork_request(&self, peers: Vec<PeerId>, hash: BlockHash, number: BlockNumber);
}

impl<T, BlockHash, BlockNumber> NetworkSyncForkRequest<BlockHash, BlockNumber> for Arc<T>
where
	T: ?Sized,
	T: NetworkSyncForkRequest<BlockHash, BlockNumber>,
{
	fn set_sync_fork_request(&self, peers: Vec<PeerId>, hash: BlockHash, number: BlockNumber) {
		T::set_sync_fork_request(self, peers, hash, number)
	}
}

/// Overview status of the network.
#[derive(Clone)]
pub struct NetworkStatus {
	/// Total number of connected peers.
	pub num_connected_peers: usize,
	/// The total number of bytes received.
	pub total_bytes_inbound: u64,
	/// The total number of bytes sent.
	pub total_bytes_outbound: u64,
}

/// Provides high-level status information about network.
#[async_trait::async_trait]
pub trait NetworkStatusProvider {
	/// High-level network status information.
	///
	/// Returns an error if the `NetworkWorker` is no longer running.
	async fn status(&self) -> Result<NetworkStatus, ()>;
}

// Manual implementation to avoid extra boxing here
impl<T> NetworkStatusProvider for Arc<T>
where
	T: ?Sized,
	T: NetworkStatusProvider,
{
	fn status<'life0, 'async_trait>(
		&'life0 self,
	) -> Pin<Box<dyn Future<Output = Result<NetworkStatus, ()>> + Send + 'async_trait>>
	where
		'life0: 'async_trait,
		Self: 'async_trait,
	{
		T::status(self)
	}
}

/// Provides low-level API for manipulating network peers.
pub trait NetworkPeers {
	/// Set authorized peers.
	///
	/// Need a better solution to manage authorized peers, but now just use reserved peers for
	/// prototyping.
	fn set_authorized_peers(&self, peers: HashSet<PeerId>);

	/// Set authorized_only flag.
	///
	/// Need a better solution to decide authorized_only, but now just use reserved_only flag for
	/// prototyping.
	fn set_authorized_only(&self, reserved_only: bool);

	/// Adds an address known to a node.
	fn add_known_address(&self, peer_id: PeerId, addr: Multiaddr);

	/// Report a given peer as either beneficial (+) or costly (-) according to the
	/// given scalar.
	fn report_peer(&self, who: PeerId, cost_benefit: ReputationChange);

	/// Disconnect from a node as soon as possible.
	///
	/// This triggers the same effects as if the connection had closed itself spontaneously.
	fn disconnect_peer(&self, who: PeerId, protocol: ProtocolName);

	/// Connect to unreserved peers and allow unreserved peers to connect for syncing purposes.
	fn accept_unreserved_peers(&self);

	/// Disconnect from unreserved peers and deny new unreserved peers to connect for syncing
	/// purposes.
	fn deny_unreserved_peers(&self);

	/// Adds a `PeerId` and its `Multiaddr` as reserved for a sync protocol (default peer set).
	///
	/// Returns an `Err` if the given string is not a valid multiaddress
	/// or contains an invalid peer ID (which includes the local peer ID).
	fn add_reserved_peer(&self, peer: MultiaddrWithPeerId) -> Result<(), String>;

	/// Removes a `PeerId` from the list of reserved peers for a sync protocol (default peer set).
	fn remove_reserved_peer(&self, peer_id: PeerId);

	/// Sets the reserved set of a protocol to the given set of peers.
	///
	/// Each `Multiaddr` must end with a `/p2p/` component containing the `PeerId`. It can also
	/// consist of only `/p2p/<peerid>`.
	///
	/// The node will start establishing/accepting connections and substreams to/from peers in this
	/// set, if it doesn't have any substream open with them yet.
	///
	/// Note however, if a call to this function results in less peers on the reserved set, they
	/// will not necessarily get disconnected (depending on available free slots in the peer set).
	/// If you want to also disconnect those removed peers, you will have to call
	/// `remove_from_peers_set` on those in addition to updating the reserved set. You can omit
	/// this step if the peer set is in reserved only mode.
	///
	/// Returns an `Err` if one of the given addresses is invalid or contains an
	/// invalid peer ID (which includes the local peer ID).
	fn set_reserved_peers(
		&self,
		protocol: ProtocolName,
		peers: HashSet<Multiaddr>,
	) -> Result<(), String>;

	/// Add peers to a peer set.
	///
	/// Each `Multiaddr` must end with a `/p2p/` component containing the `PeerId`. It can also
	/// consist of only `/p2p/<peerid>`.
	///
	/// Returns an `Err` if one of the given addresses is invalid or contains an
	/// invalid peer ID (which includes the local peer ID).
	fn add_peers_to_reserved_set(
		&self,
		protocol: ProtocolName,
		peers: HashSet<Multiaddr>,
	) -> Result<(), String>;

	/// Remove peers from a peer set.
	fn remove_peers_from_reserved_set(&self, protocol: ProtocolName, peers: Vec<PeerId>);

	/// Returns the number of peers in the sync peer set we're connected to.
	fn sync_num_connected(&self) -> usize;
}

// Manual implementation to avoid extra boxing here
impl<T> NetworkPeers for Arc<T>
where
	T: ?Sized,
	T: NetworkPeers,
{
	fn set_authorized_peers(&self, peers: HashSet<PeerId>) {
		T::set_authorized_peers(self, peers)
	}

	fn set_authorized_only(&self, reserved_only: bool) {
		T::set_authorized_only(self, reserved_only)
	}

	fn add_known_address(&self, peer_id: PeerId, addr: Multiaddr) {
		T::add_known_address(self, peer_id, addr)
	}

	fn report_peer(&self, who: PeerId, cost_benefit: ReputationChange) {
		// TODO: when we get rid of `Peerset`, we'll likely need to add some kind of async
		// interface to `PeerStore`, otherwise we'll have trouble calling functions accepting
		// `&mut self` via `Arc`.
		// See https://github.com/paritytech/substrate/issues/14170.
		T::report_peer(self, who, cost_benefit)
	}

	fn disconnect_peer(&self, who: PeerId, protocol: ProtocolName) {
		T::disconnect_peer(self, who, protocol)
	}

	fn accept_unreserved_peers(&self) {
		T::accept_unreserved_peers(self)
	}

	fn deny_unreserved_peers(&self) {
		T::deny_unreserved_peers(self)
	}

	fn add_reserved_peer(&self, peer: MultiaddrWithPeerId) -> Result<(), String> {
		T::add_reserved_peer(self, peer)
	}

	fn remove_reserved_peer(&self, peer_id: PeerId) {
		T::remove_reserved_peer(self, peer_id)
	}

	fn set_reserved_peers(
		&self,
		protocol: ProtocolName,
		peers: HashSet<Multiaddr>,
	) -> Result<(), String> {
		T::set_reserved_peers(self, protocol, peers)
	}

	fn add_peers_to_reserved_set(
		&self,
		protocol: ProtocolName,
		peers: HashSet<Multiaddr>,
	) -> Result<(), String> {
		T::add_peers_to_reserved_set(self, protocol, peers)
	}

	fn remove_peers_from_reserved_set(&self, protocol: ProtocolName, peers: Vec<PeerId>) {
		T::remove_peers_from_reserved_set(self, protocol, peers)
	}

	fn sync_num_connected(&self) -> usize {
		T::sync_num_connected(self)
	}
}

/// Provides access to network-level event stream.
pub trait NetworkEventStream {
	/// Returns a stream containing the events that happen on the network.
	///
	/// If this method is called multiple times, the events are duplicated.
	///
	/// The stream never ends (unless the `NetworkWorker` gets shut down).
	///
	/// The name passed is used to identify the channel in the Prometheus metrics. Note that the
	/// parameter is a `&'static str`, and not a `String`, in order to avoid accidentally having
	/// an unbounded set of Prometheus metrics, which would be quite bad in terms of memory
	fn event_stream(&self, name: &'static str) -> Pin<Box<dyn Stream<Item = Event> + Send>>;
}

impl<T> NetworkEventStream for Arc<T>
where
	T: ?Sized,
	T: NetworkEventStream,
{
	fn event_stream(&self, name: &'static str) -> Pin<Box<dyn Stream<Item = Event> + Send>> {
		T::event_stream(self, name)
	}
}

/// Trait for providing information about the local network state
pub trait NetworkStateInfo {
	/// Returns the local external addresses.
	fn external_addresses(&self) -> Vec<Multiaddr>;

	/// Returns the listening addresses (without trailing `/p2p/` with our `PeerId`).
	fn listen_addresses(&self) -> Vec<Multiaddr>;

	/// Returns the local Peer ID.
	fn local_peer_id(&self) -> PeerId;
}

impl<T> NetworkStateInfo for Arc<T>
where
	T: ?Sized,
	T: NetworkStateInfo,
{
	fn external_addresses(&self) -> Vec<Multiaddr> {
		T::external_addresses(self)
	}

	fn listen_addresses(&self) -> Vec<Multiaddr> {
		T::listen_addresses(self)
	}

	fn local_peer_id(&self) -> PeerId {
		T::local_peer_id(self)
	}
}

/// Reserved slot in the notifications buffer, ready to accept data.
pub trait NotificationSenderReady {
	/// Consumes this slots reservation and actually queues the notification.
	///
	/// NOTE: Traits can't consume itself, but calling this method second time will return an error.
	fn send(&mut self, notification: Vec<u8>) -> Result<(), NotificationSenderError>;
}

/// A `NotificationSender` allows for sending notifications to a peer with a chosen protocol.
#[async_trait::async_trait]
pub trait NotificationSender: Send + Sync + 'static {
	/// Returns a future that resolves when the `NotificationSender` is ready to send a
	/// notification.
	async fn ready(&self)
		-> Result<Box<dyn NotificationSenderReady + '_>, NotificationSenderError>;
}

/// Error returned by [`NetworkNotification::notification_sender`].
#[derive(Debug, thiserror::Error)]
pub enum NotificationSenderError {
	/// The notification receiver has been closed, usually because the underlying connection
	/// closed.
	///
	/// Some of the notifications most recently sent may not have been received. However,
	/// the peer may still be connected and a new `NotificationSender` for the same
	/// protocol obtained from [`NetworkNotification::notification_sender`].
	#[error("The notification receiver has been closed")]
	Closed,
	/// Protocol name hasn't been registered.
	#[error("Protocol name hasn't been registered")]
	BadProtocol,
}

/// Provides ability to send network notifications.
pub trait NetworkNotification {
	/// Appends a notification to the buffer of pending outgoing notifications with the given peer.
	/// Has no effect if the notifications channel with this protocol name is not open.
	///
	/// If the buffer of pending outgoing notifications with that peer is full, the notification
	/// is silently dropped and the connection to the remote will start being shut down. This
	/// happens if you call this method at a higher rate than the rate at which the peer processes
	/// these notifications, or if the available network bandwidth is too low.
	///
	/// For this reason, this method is considered soft-deprecated. You are encouraged to use
	/// [`NetworkNotification::notification_sender`] instead.
	///
	/// > **Note**: The reason why this is a no-op in the situation where we have no channel is
	/// >			that we don't guarantee message delivery anyway. Networking issues can cause
	/// >			connections to drop at any time, and higher-level logic shouldn't differentiate
	/// >			between the remote voluntarily closing a substream or a network error
	/// >			preventing the message from being delivered.
	///
	/// The protocol must have been registered with
	/// `crate::config::NetworkConfiguration::notifications_protocols`.
	fn write_notification(&self, target: PeerId, protocol: ProtocolName, message: Vec<u8>);

	/// Obtains a [`NotificationSender`] for a connected peer, if it exists.
	///
	/// A `NotificationSender` is scoped to a particular connection to the peer that holds
	/// a receiver. With a `NotificationSender` at hand, sending a notification is done in two
	/// steps:
	///
	/// 1.  [`NotificationSender::ready`] is used to wait for the sender to become ready
	/// for another notification, yielding a [`NotificationSenderReady`] token.
	/// 2.  [`NotificationSenderReady::send`] enqueues the notification for sending. This operation
	/// can only fail if the underlying notification substream or connection has suddenly closed.
	///
	/// An error is returned by [`NotificationSenderReady::send`] if there exists no open
	/// notifications substream with that combination of peer and protocol, or if the remote
	/// has asked to close the notifications substream. If that happens, it is guaranteed that an
	/// [`Event::NotificationStreamClosed`] has been generated on the stream returned by
	/// [`NetworkEventStream::event_stream`].
	///
	/// If the remote requests to close the notifications substream, all notifications successfully
	/// enqueued using [`NotificationSenderReady::send`] will finish being sent out before the
	/// substream actually gets closed, but attempting to enqueue more notifications will now
	/// return an error. It is however possible for the entire connection to be abruptly closed,
	/// in which case enqueued notifications will be lost.
	///
	/// The protocol must have been registered with
	/// `crate::config::NetworkConfiguration::notifications_protocols`.
	///
	/// # Usage
	///
	/// This method returns a struct that allows waiting until there is space available in the
	/// buffer of messages towards the given peer. If the peer processes notifications at a slower
	/// rate than we send them, this buffer will quickly fill up.
	///
	/// As such, you should never do something like this:
	///
	/// ```ignore
	/// // Do NOT do this
	/// for peer in peers {
	/// 	if let Ok(n) = network.notification_sender(peer, ...) {
	/// 			if let Ok(s) = n.ready().await {
	/// 				let _ = s.send(...);
	/// 			}
	/// 	}
	/// }
	/// ```
	///
	/// Doing so would slow down all peers to the rate of the slowest one. A malicious or
	/// malfunctioning peer could intentionally process notifications at a very slow rate.
	///
	/// Instead, you are encouraged to maintain your own buffer of notifications on top of the one
	/// maintained by `sc-network`, and use `notification_sender` to progressively send out
	/// elements from your buffer. If this additional buffer is full (which will happen at some
	/// point if the peer is too slow to process notifications), appropriate measures can be taken,
	/// such as removing non-critical notifications from the buffer or disconnecting the peer
	/// using [`NetworkPeers::disconnect_peer`].
	///
	///
	/// Notifications              Per-peer buffer
	///   broadcast    +------->   of notifications   +-->  `notification_sender`  +-->  Internet
	///                    ^       (not covered by
	///                    |         sc-network)
	///                    +
	///      Notifications should be dropped
	///             if buffer is full
	///
	///
	/// See also the `sc-network-gossip` crate for a higher-level way to send notifications.
	fn notification_sender(
		&self,
		target: PeerId,
		protocol: ProtocolName,
	) -> Result<Box<dyn NotificationSender>, NotificationSenderError>;

	/// Set handshake for the notification protocol.
	fn set_notification_handshake(&self, protocol: ProtocolName, handshake: Vec<u8>);
}

impl<T> NetworkNotification for Arc<T>
where
	T: ?Sized,
	T: NetworkNotification,
{
	fn write_notification(&self, target: PeerId, protocol: ProtocolName, message: Vec<u8>) {
		T::write_notification(self, target, protocol, message)
	}

	fn notification_sender(
		&self,
		target: PeerId,
		protocol: ProtocolName,
	) -> Result<Box<dyn NotificationSender>, NotificationSenderError> {
		T::notification_sender(self, target, protocol)
	}

	fn set_notification_handshake(&self, protocol: ProtocolName, handshake: Vec<u8>) {
		T::set_notification_handshake(self, protocol, handshake)
	}
}

/// Provides ability to send network requests.
#[async_trait::async_trait]
pub trait NetworkRequest {
	/// Sends a single targeted request to a specific peer. On success, returns the response of
	/// the peer.
	///
	/// Request-response protocols are a way to complement notifications protocols, but
	/// notifications should remain the default ways of communicating information. For example, a
	/// peer can announce something through a notification, after which the recipient can obtain
	/// more information by performing a request.
	/// As such, call this function with `IfDisconnected::ImmediateError` for `connect`. This way
	/// you will get an error immediately for disconnected peers, instead of waiting for a
	/// potentially very long connection attempt, which would suggest that something is wrong
	/// anyway, as you are supposed to be connected because of the notification protocol.
	///
	/// No limit or throttling of concurrent outbound requests per peer and protocol are enforced.
	/// Such restrictions, if desired, need to be enforced at the call site(s).
	///
	/// The protocol must have been registered through
	/// `NetworkConfiguration::request_response_protocols`.
	async fn request(
		&self,
		target: PeerId,
		protocol: ProtocolName,
		request: Vec<u8>,
		connect: IfDisconnected,
	) -> Result<Vec<u8>, RequestFailure>;

	/// Variation of `request` which starts a request whose response is delivered on a provided
	/// channel.
	///
	/// Instead of blocking and waiting for a reply, this function returns immediately, sending
	/// responses via the passed in sender. This alternative API exists to make it easier to
	/// integrate with message passing APIs.
	///
	/// Keep in mind that the connected receiver might receive a `Canceled` event in case of a
	/// closing connection. This is expected behaviour. With `request` you would get a
	/// `RequestFailure::Network(OutboundFailure::ConnectionClosed)` in that case.
	fn start_request(
		&self,
		target: PeerId,
		protocol: ProtocolName,
		request: Vec<u8>,
		tx: oneshot::Sender<Result<Vec<u8>, RequestFailure>>,
		connect: IfDisconnected,
	);
}

// Manual implementation to avoid extra boxing here
impl<T> NetworkRequest for Arc<T>
where
	T: ?Sized,
	T: NetworkRequest,
{
	fn request<'life0, 'async_trait>(
		&'life0 self,
		target: PeerId,
		protocol: ProtocolName,
		request: Vec<u8>,
		connect: IfDisconnected,
	) -> Pin<Box<dyn Future<Output = Result<Vec<u8>, RequestFailure>> + Send + 'async_trait>>
	where
		'life0: 'async_trait,
		Self: 'async_trait,
	{
		T::request(self, target, protocol, request, connect)
	}

	fn start_request(
		&self,
		target: PeerId,
		protocol: ProtocolName,
		request: Vec<u8>,
		tx: oneshot::Sender<Result<Vec<u8>, RequestFailure>>,
		connect: IfDisconnected,
	) {
		T::start_request(self, target, protocol, request, tx, connect)
	}
}

/// Provides ability to announce blocks to the network.
pub trait NetworkBlock<BlockHash, BlockNumber> {
	/// Make sure an important block is propagated to peers.
	///
	/// In chain-based consensus, we often need to make sure non-best forks are
	/// at least temporarily synced. This function forces such an announcement.
	fn announce_block(&self, hash: BlockHash, data: Option<Vec<u8>>);

	/// Inform the network service about new best imported block.
	fn new_best_block_imported(&self, hash: BlockHash, number: BlockNumber);
}

impl<T, BlockHash, BlockNumber> NetworkBlock<BlockHash, BlockNumber> for Arc<T>
where
	T: ?Sized,
	T: NetworkBlock<BlockHash, BlockNumber>,
{
	fn announce_block(&self, hash: BlockHash, data: Option<Vec<u8>>) {
		T::announce_block(self, hash, data)
	}

	fn new_best_block_imported(&self, hash: BlockHash, number: BlockNumber) {
		T::new_best_block_imported(self, hash, number)
	}
}
