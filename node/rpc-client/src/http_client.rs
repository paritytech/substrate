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

use hyper::{http, Client, Request};
use hyper::rt;
use futures::{sync::mpsc, Future, Stream, Sink};

use jsonrpc_core_client::{RpcClient, RpcChannel, RpcError};

fn http_client(url: &str) -> (
	impl Future<Item = (), Error = ()>,
	impl Sink<SinkItem = String, SinkError = RpcError>,
	impl Stream<Item = String, Error = RpcError>
) {
	let url = url.to_owned();
	let client = Client::new();
	let (requests, requests_rx) = mpsc::channel(8);
	let (responses, responses_rx) = mpsc::channel(0);

	let future = requests_rx
		.map(move |request: String| {
			let request = Request::post(&url)
				.header(http::header::CONTENT_TYPE, http::header::HeaderValue::from_static("application/json"))
				.body(request.into())
				.unwrap();

			client
				.request(request)
				.map_err(|e| RpcError::Other(e.into()))
				.and_then(|res| {
					// TODO [ToDr] Handle non-200
					res.into_body()
						.map_err(|e| RpcError::ParseError(e.to_string(), e.into()))
						.concat2()
						.map(|chunk| String::from_utf8_lossy(chunk.as_ref()).into_owned())
				})
		})
		.forward(responses
			.sink_map_err(|_e| ())
		)
		.map(|_| ())
		;

	(
		future,
		requests.sink_map_err(|e| RpcError::Other(e.into())),
		responses_rx
			.map_err(|()| unreachable!())
			.and_then(|res| res)
	)
}

pub fn http<TClient: From<RpcChannel>>(url: &str) -> impl Future<Item=TClient, Error=()> {
	let (run, sink, stream) = http_client(url);
	let (sender, receiver) = mpsc::channel(0);
	let rpc_client = RpcClient::new(sink, stream, receiver);


	(
		rt::lazy(move || {
			rt::spawn(run);
			rt::spawn(rpc_client.map_err(|e| {
				log::error!("RPC Client error: {:?}", e);
			}));
			Ok(sender.into())
		})
	)
}
