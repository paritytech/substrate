// Copyright 2017 Parity Technologies (UK) Ltd.
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

extern crate substrate_rpc as apis;

extern crate jsonrpc_core as rpc;
extern crate jsonrpc_http_server as http;

use std::io;

/// Construct rpc `IoHandler`
pub fn rpc_handler<S>(state: S) -> rpc::IoHandler where
	S: apis::state::StateApi,
{
	let mut io = rpc::IoHandler::new();
	io.extend_with(state.to_delegate());
	io
}

/// Start HTTP server listening on given address.
pub fn start_http(
	addr: &std::net::SocketAddr,
	io: rpc::IoHandler,
) -> io::Result<http::Server> {
	http::ServerBuilder::new(io)
		.threads(4)
		.rest_api(http::RestApi::Unsecure)
		.start_http(addr)
}
