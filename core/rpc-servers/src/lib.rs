// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

//! Substrate RPC servers.

#[warn(missing_docs)]

pub extern crate substrate_rpc as apis;

extern crate jsonrpc_http_server as http;
extern crate jsonrpc_pubsub as pubsub;
extern crate jsonrpc_ws_server as ws;
extern crate serde;
extern crate sr_primitives;

#[macro_use]
extern crate log;

use std::io;
use sr_primitives::{traits::{Block as BlockT, NumberFor}, generic::SignedBlock};

/// Maximal payload accepted by RPC servers
const MAX_PAYLOAD: usize = 15 * 1024 * 1024;

type Metadata = apis::metadata::Metadata;
type RpcHandler = pubsub::PubSubHandler<Metadata>;
pub type HttpServer = http::Server;
pub type WsServer = ws::Server;

/// Construct rpc `IoHandler`
pub fn rpc_handler<Block: BlockT, ExHash, S, C, A, Y>(
	state: S,
	chain: C,
	author: A,
	system: Y,
) -> RpcHandler where
	Block: BlockT + 'static,
	ExHash: Send + Sync + 'static + sr_primitives::Serialize + sr_primitives::DeserializeOwned,
	SignedBlock<Block>: serde::Serialize + sr_primitives::DeserializeOwned,
	S: apis::state::StateApi<Block::Hash, Metadata=Metadata>,
	C: apis::chain::ChainApi<Block::Hash, Block::Header, NumberFor<Block>, SignedBlock<Block>, Metadata=Metadata>,
	A: apis::author::AuthorApi<ExHash, Block::Hash, Metadata=Metadata>,
	Y: apis::system::SystemApi,
{
	let mut io = pubsub::PubSubHandler::default();
	io.extend_with(state.to_delegate());
	io.extend_with(chain.to_delegate());
	io.extend_with(author.to_delegate());
	io.extend_with(system.to_delegate());
	io
}

/// Start HTTP server listening on given address.
pub fn start_http(
	addr: &std::net::SocketAddr,
	io: RpcHandler,
) -> io::Result<http::Server> {
	http::ServerBuilder::new(io)
		.threads(4)
		.health_api(("/health", "system_health"))
		.rest_api(http::RestApi::Unsecure)
		.cors(http::DomainsValidation::Disabled)
		.max_request_body_size(MAX_PAYLOAD)
		.start_http(addr)
}

/// Start WS server listening on given address.
pub fn start_ws(
	addr: &std::net::SocketAddr,
	io: RpcHandler,
) -> io::Result<ws::Server> {
	ws::ServerBuilder::with_meta_extractor(io, |context: &ws::RequestContext| Metadata::new(context.sender()))
		.max_payload(MAX_PAYLOAD)
		.start(addr)
		.map_err(|err| match err {
			ws::Error(ws::ErrorKind::Io(io), _) => io,
			ws::Error(ws::ErrorKind::ConnectionClosed, _) => io::ErrorKind::BrokenPipe.into(),
			ws::Error(e, _) => {
				error!("{}", e);
				io::ErrorKind::Other.into()
			}
		})
}
