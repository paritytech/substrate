// Copyright 2022 Parity Technologies (UK) Ltd.
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

//! Bitswap server for substrate.
//!
//! Allows querying transactions by hash over standard bitswap protocol
//! Only supports bitswap 1.2.0.
//! CID is expected to reference 256-bit Blake2b transaction hash.

use crate::schema::bitswap::{
	message::{wantlist::WantType, Block as MessageBlock, BlockPresence, BlockPresenceType},
	Message as BitswapMessage,
};
use cid::Version;
use core::pin::Pin;
use futures::{
	io::{AsyncRead, AsyncWrite},
	Future,
};
use libp2p::{
	core::{
		connection::ConnectionId, upgrade, InboundUpgrade, Multiaddr, OutboundUpgrade, PeerId,
		UpgradeInfo,
	},
	swarm::{
		NetworkBehaviour, NetworkBehaviourAction, NotifyHandler, OneShotHandler, PollParameters,
	},
};
use log::{debug, error, trace};
use prost::Message;
use sc_client_api::BlockBackend;
use sp_runtime::traits::Block as BlockT;
use std::{
	collections::VecDeque,
	io,
	marker::PhantomData,
	sync::Arc,
	task::{Context, Poll},
};
use unsigned_varint::encode as varint_encode;

const LOG_TARGET: &str = "bitswap";

// Undocumented, but according to JS the bitswap messages have a max size of 512*1024 bytes
// https://github.com/ipfs/js-ipfs-bitswap/blob/
// d8f80408aadab94c962f6b88f343eb9f39fa0fcc/src/decision-engine/index.js#L16
// We set it to the same value as max substrate protocol message
const MAX_PACKET_SIZE: usize = 16 * 1024 * 1024;

// Max number of queued responses before denying requests.
const MAX_RESPONSE_QUEUE: usize = 20;
// Max number of blocks per wantlist
const MAX_WANTED_BLOCKS: usize = 16;

const PROTOCOL_NAME: &[u8] = b"/ipfs/bitswap/1.2.0";

type FutureResult<T, E> = Pin<Box<dyn Future<Output = Result<T, E>> + Send>>;

/// Bitswap protocol config
#[derive(Clone, Copy, Debug, Default)]
pub struct BitswapConfig;

impl UpgradeInfo for BitswapConfig {
	type Info = &'static [u8];
	type InfoIter = std::iter::Once<Self::Info>;

	fn protocol_info(&self) -> Self::InfoIter {
		std::iter::once(PROTOCOL_NAME)
	}
}

impl<TSocket> InboundUpgrade<TSocket> for BitswapConfig
where
	TSocket: AsyncRead + AsyncWrite + Send + Unpin + 'static,
{
	type Output = BitswapMessage;
	type Error = BitswapError;
	type Future = FutureResult<Self::Output, Self::Error>;

	fn upgrade_inbound(self, mut socket: TSocket, _info: Self::Info) -> Self::Future {
		Box::pin(async move {
			let packet = upgrade::read_length_prefixed(&mut socket, MAX_PACKET_SIZE).await?;
			let message: BitswapMessage = Message::decode(packet.as_slice())?;
			Ok(message)
		})
	}
}

impl UpgradeInfo for BitswapMessage {
	type Info = &'static [u8];
	type InfoIter = std::iter::Once<Self::Info>;

	fn protocol_info(&self) -> Self::InfoIter {
		std::iter::once(PROTOCOL_NAME)
	}
}

impl<TSocket> OutboundUpgrade<TSocket> for BitswapMessage
where
	TSocket: AsyncRead + AsyncWrite + Send + Unpin + 'static,
{
	type Output = ();
	type Error = io::Error;
	type Future = FutureResult<Self::Output, Self::Error>;

	fn upgrade_outbound(self, mut socket: TSocket, _info: Self::Info) -> Self::Future {
		Box::pin(async move {
			let data = self.encode_to_vec();
			upgrade::write_length_prefixed(&mut socket, data).await
		})
	}
}

/// Internal protocol handler event.
#[derive(Debug)]
pub enum HandlerEvent {
	/// We received a `BitswapMessage` from a remote.
	Request(BitswapMessage),
	/// We successfully sent a `BitswapMessage`.
	ResponseSent,
}

impl From<BitswapMessage> for HandlerEvent {
	fn from(message: BitswapMessage) -> Self {
		Self::Request(message)
	}
}

impl From<()> for HandlerEvent {
	fn from(_: ()) -> Self {
		Self::ResponseSent
	}
}

/// Prefix represents all metadata of a CID, without the actual content.
#[derive(PartialEq, Eq, Clone, Debug)]
struct Prefix {
	/// The version of CID.
	pub version: Version,
	/// The codec of CID.
	pub codec: u64,
	/// The multihash type of CID.
	pub mh_type: u64,
	/// The multihash length of CID.
	pub mh_len: u8,
}

impl Prefix {
	/// Convert the prefix to encoded bytes.
	pub fn to_bytes(&self) -> Vec<u8> {
		let mut res = Vec::with_capacity(4);
		let mut buf = varint_encode::u64_buffer();
		let version = varint_encode::u64(self.version.into(), &mut buf);
		res.extend_from_slice(version);
		let mut buf = varint_encode::u64_buffer();
		let codec = varint_encode::u64(self.codec, &mut buf);
		res.extend_from_slice(codec);
		let mut buf = varint_encode::u64_buffer();
		let mh_type = varint_encode::u64(self.mh_type, &mut buf);
		res.extend_from_slice(mh_type);
		let mut buf = varint_encode::u64_buffer();
		let mh_len = varint_encode::u64(self.mh_len as u64, &mut buf);
		res.extend_from_slice(mh_len);
		res
	}
}

/// Bitswap trait
pub trait BitswapT<B: BlockT> {
	/// Get single indexed transaction by content hash.
	///
	/// Note that this will only fetch transactions
	/// that are indexed by the runtime with `storage_index_transaction`.
	fn indexed_transaction(
		&self,
		hash: <B as BlockT>::Hash,
	) -> sp_blockchain::Result<Option<Vec<u8>>>;

	/// Queue of blocks ready to be sent out on `poll()`
	fn ready_blocks(&mut self) -> &mut VecDeque<(PeerId, BitswapMessage)>;
}

/// Network behaviour that handles sending and receiving IPFS blocks.
struct BitswapInternal<B, Client> {
	client: Arc<Client>,
	ready_blocks: VecDeque<(PeerId, BitswapMessage)>,
	_block: PhantomData<B>,
}

impl<B, Client> BitswapInternal<B, Client> {
	/// Create a new instance of the bitswap protocol handler.
	pub fn new(client: Arc<Client>) -> Self {
		Self { client, ready_blocks: Default::default(), _block: PhantomData::default() }
	}
}

impl<Block, Client> BitswapT<Block> for BitswapInternal<Block, Client>
where
	Block: BlockT,
	Client: BlockBackend<Block>,
{
	fn indexed_transaction(
		&self,
		hash: <Block as BlockT>::Hash,
	) -> sp_blockchain::Result<Option<Vec<u8>>> {
		self.client.indexed_transaction(&hash)
	}

	fn ready_blocks(&mut self) -> &mut VecDeque<(PeerId, BitswapMessage)> {
		&mut self.ready_blocks
	}
}

/// Wrapper for bitswap trait object  implement NetworkBehaviour
pub struct Bitswap<Block: BlockT> {
	inner: Box<dyn BitswapT<Block> + Sync + Send>,
}

impl<B: BlockT> Bitswap<B> {
	/// Create new Bitswap wrapper
	pub fn from_client<Client: BlockBackend<B> + Send + Sync + 'static>(
		client: Arc<Client>,
	) -> Self {
		let inner = Box::new(BitswapInternal::new(client)) as Box<_>;
		Self { inner }
	}
}

impl<Block: BlockT> BitswapT<Block> for Bitswap<Block> {
	fn indexed_transaction(
		&self,
		hash: <Block as BlockT>::Hash,
	) -> sp_blockchain::Result<Option<Vec<u8>>> {
		self.inner.indexed_transaction(hash)
	}

	fn ready_blocks(&mut self) -> &mut VecDeque<(PeerId, BitswapMessage)> {
		self.inner.ready_blocks()
	}
}

impl<Block: BlockT, T> BitswapT<Block> for Box<T>
where
	T: BitswapT<Block>,
{
	fn indexed_transaction(
		&self,
		hash: <Block as BlockT>::Hash,
	) -> sp_blockchain::Result<Option<Vec<u8>>> {
		T::indexed_transaction(self, hash)
	}

	fn ready_blocks(&mut self) -> &mut VecDeque<(PeerId, BitswapMessage)> {
		T::ready_blocks(self)
	}
}

impl<B> NetworkBehaviour for Bitswap<B>
where
	B: BlockT,
{
	type ConnectionHandler = OneShotHandler<BitswapConfig, BitswapMessage, HandlerEvent>;
	type OutEvent = void::Void;

	fn new_handler(&mut self) -> Self::ConnectionHandler {
		Default::default()
	}

	fn addresses_of_peer(&mut self, _peer: &PeerId) -> Vec<Multiaddr> {
		Vec::new()
	}

	fn inject_event(&mut self, peer: PeerId, _connection: ConnectionId, message: HandlerEvent) {
		let request = match message {
			HandlerEvent::ResponseSent => return,
			HandlerEvent::Request(msg) => msg,
		};
		trace!(target: LOG_TARGET, "Received request: {:?} from {}", request, peer);
		if self.ready_blocks().len() > MAX_RESPONSE_QUEUE {
			debug!(target: LOG_TARGET, "Ignored request: queue is full");
			return
		}

		let mut response = BitswapMessage {
			wantlist: None,
			blocks: Default::default(),
			payload: Default::default(),
			block_presences: Default::default(),
			pending_bytes: 0,
		};
		let wantlist = match request.wantlist {
			Some(wantlist) => wantlist,
			None => {
				debug!(target: LOG_TARGET, "Unexpected bitswap message from {}", peer);
				return
			},
		};
		if wantlist.entries.len() > MAX_WANTED_BLOCKS {
			trace!(target: LOG_TARGET, "Ignored request: too many entries");
			return
		}
		for entry in wantlist.entries {
			let cid = match cid::Cid::read_bytes(entry.block.as_slice()) {
				Ok(cid) => cid,
				Err(e) => {
					trace!(target: LOG_TARGET, "Bad CID {:?}: {:?}", entry.block, e);
					continue
				},
			};
			if cid.version() != cid::Version::V1 ||
				cid.hash().code() != u64::from(cid::multihash::Code::Blake2b256) ||
				cid.hash().size() != 32
			{
				debug!(target: LOG_TARGET, "Ignoring unsupported CID {}: {}", peer, cid);
				continue
			}
			let mut hash = B::Hash::default();
			hash.as_mut().copy_from_slice(&cid.hash().digest()[0..32]);
			let transaction = match self.indexed_transaction(hash) {
				Ok(ex) => ex,
				Err(e) => {
					error!(target: LOG_TARGET, "Error retrieving transaction {}: {}", hash, e);
					None
				},
			};
			match transaction {
				Some(transaction) => {
					trace!(target: LOG_TARGET, "Found CID {:?}, hash {:?}", cid, hash);
					if entry.want_type == WantType::Block as i32 {
						let prefix = Prefix {
							version: cid.version(),
							codec: cid.codec(),
							mh_type: cid.hash().code(),
							mh_len: cid.hash().size(),
						};
						response
							.payload
							.push(MessageBlock { prefix: prefix.to_bytes(), data: transaction });
					} else {
						response.block_presences.push(BlockPresence {
							r#type: BlockPresenceType::Have as i32,
							cid: cid.to_bytes(),
						});
					}
				},
				None => {
					trace!(target: LOG_TARGET, "Missing CID {:?}, hash {:?}", cid, hash);
					if entry.send_dont_have {
						response.block_presences.push(BlockPresence {
							r#type: BlockPresenceType::DontHave as i32,
							cid: cid.to_bytes(),
						});
					}
				},
			}
		}
		trace!(target: LOG_TARGET, "Response: {:?}", response);
		self.ready_blocks().push_back((peer, response));
	}

	fn poll(
		&mut self,
		_ctx: &mut Context,
		_: &mut impl PollParameters,
	) -> Poll<NetworkBehaviourAction<Self::OutEvent, Self::ConnectionHandler>> {
		if let Some((peer_id, message)) = self.ready_blocks().pop_front() {
			return Poll::Ready(NetworkBehaviourAction::NotifyHandler {
				peer_id,
				handler: NotifyHandler::Any,
				event: message,
			})
		}
		Poll::Pending
	}
}

/// Bitswap protocol error.
#[derive(Debug, thiserror::Error)]
pub enum BitswapError {
	/// Protobuf decoding error.
	#[error("Failed to decode request: {0}.")]
	DecodeProto(#[from] prost::DecodeError),

	/// Protobuf encoding error.
	#[error("Failed to encode response: {0}.")]
	EncodeProto(#[from] prost::EncodeError),

	/// Client backend error.
	#[error(transparent)]
	Client(#[from] sp_blockchain::Error),

	/// Error parsing CID
	#[error(transparent)]
	BadCid(#[from] cid::Error),

	/// Packet read error.
	#[error(transparent)]
	Read(#[from] io::Error),

	/// Error sending response.
	#[error("Failed to send response.")]
	SendResponse,
}
