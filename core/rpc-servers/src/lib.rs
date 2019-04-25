// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Substrate RPC servers.

#[warn(missing_docs)]

pub use substrate_rpc as apis;

use std::io;
use log::error;
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
	S: apis::state::StateApi<Block::Hash, Metadata=Metadata>,
	C: apis::chain::ChainApi<NumberFor<Block>, Block::Hash, Block::Header, SignedBlock<Block>, Metadata=Metadata>,
	A: apis::author::AuthorApi<ExHash, Block::Hash, Metadata=Metadata>,
	Y: apis::system::SystemApi<Block::Hash, NumberFor<Block>>,
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
