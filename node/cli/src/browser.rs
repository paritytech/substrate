// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

#![cfg(feature = "browser")]

use crate::ChainSpec;
use futures::{prelude::*, sync::oneshot, sync::mpsc};
use libp2p::wasm_ext;
use log::{debug, info};
use std::sync::Arc;
use substrate_service::{AbstractService, RpcSession, Roles as ServiceRoles, Configuration, config::DatabaseConfig};
use wasm_bindgen::prelude::*;

/// Starts the client.
#[wasm_bindgen]
pub fn start_client(wasm_ext: wasm_ext::ffi::Transport) -> Result<Client, JsValue> {
	start_inner(wasm_ext)
		.map_err(|err| JsValue::from_str(&err.to_string()))
}

fn start_inner(wasm_ext: wasm_ext::ffi::Transport) -> Result<Client, Box<dyn std::error::Error>> {
	console_error_panic_hook::set_once();
	console_log::init_with_level(log::Level::Info);

	let wasm_ext = wasm_ext::ExtTransport::new(wasm_ext);

	let chain_spec = ChainSpec::FlamingFir.load().map_err(|e| format!("{:?}", e))?;
	let mut config = Configuration::<(), _, _>::default_with_spec(chain_spec);
	config.network.transport = network::config::TransportConfig::Normal {
		wasm_external_transport: Some(wasm_ext.clone()),
		enable_mdns: false,
	};
	config.telemetry_external_transport = Some(wasm_ext);
	config.roles = ServiceRoles::FULL;
	config.name = "Browser node".to_string();
    config.database = {
        let db = Arc::new(kvdb_memorydb::create(10));
        DatabaseConfig::Custom(db)
    };
    // TODO: config.database

	//info!("{}", version.name);
	info!("  version {}", config.full_version());
	info!("  by Parity Technologies, 2017-2019");
	info!("Chain specification: {}", config.chain_spec.name());
	info!("Node name: {}", config.name);
	info!("Roles: {:?}", config.roles);

	let mut service = new_full!(config)
		.map_err(|e: String| format!("{:?}", e))?.0;

	/*let informant = substrate_cli::informant::build(&service);
	wasm_bindgen_futures::spawn_local(informant);*/

	let (rpc_send_tx, mut rpc_send_rx) = mpsc::unbounded::<RpcMessage>();
	wasm_bindgen_futures::spawn_local(futures::future::poll_fn(move || {
		loop {
			match rpc_send_rx.poll() {
				Ok(Async::Ready(Some(message))) => {
					let fut = service.rpc_query(&message.session, &message.rpc_json);
					let _ = message.send_back.send(Box::new(fut));
				},
				Ok(Async::NotReady) => break,
				Err(_) | Ok(Async::Ready(None)) => return Ok(Async::Ready(())),
			}
		}

		loop {
			match service.poll().map_err(|_| ())? {
				Async::Ready(()) => return Ok(Async::Ready(())),
				Async::NotReady => break
			}
		}

		Ok(Async::NotReady)
	}));

	Ok(Client {
		rpc_send_tx,
	})
}

/// A running client.
#[wasm_bindgen]
pub struct Client {
	rpc_send_tx: mpsc::UnboundedSender<RpcMessage>,
}

struct RpcMessage {
	rpc_json: String,
	session: RpcSession,
	send_back: oneshot::Sender<Box<dyn Future<Item = Option<String>, Error = ()>>>,
}

#[wasm_bindgen]
impl Client {
	/// Allows starting an RPC request. Returns a `Promise` containing the result of that request.
	#[wasm_bindgen(js_name = "rpcSend")]
	pub fn rpc_send(&mut self, rpc: &str) -> js_sys::Promise {
		let rpc_session = RpcSession::new(mpsc::channel(1).0);
		let (tx, rx) = oneshot::channel();
		let _ = self.rpc_send_tx.unbounded_send(RpcMessage {
			rpc_json: rpc.to_owned(),
			session: rpc_session,
			send_back: tx,
		});
		let fut = rx
			.map_err(|_| ())
			.and_then(|fut| fut)
			.map(|s| JsValue::from_str(&s.unwrap_or(String::new())))
			.map_err(|_| JsValue::NULL);
		wasm_bindgen_futures::future_to_promise(fut)
	}

	/// Subscribes to an RPC pubsub endpoint.
	#[wasm_bindgen(js_name = "rpcSubscribe")]
	pub fn rpc_subscribe(&mut self, rpc: &str, callback: js_sys::Function) {
		let (tx, rx) = mpsc::channel(4);
		let rpc_session = RpcSession::new(tx);
		let (fut_tx, fut_rx) = oneshot::channel();
		let _ = self.rpc_send_tx.unbounded_send(RpcMessage {
			rpc_json: rpc.to_owned(),
			session: rpc_session.clone(),
			send_back: fut_tx,
		});
		let fut_rx = fut_rx
			.map_err(|_| ())
			.and_then(|fut| fut);
		wasm_bindgen_futures::spawn_local(fut_rx.then(|_| Ok(())));
		wasm_bindgen_futures::spawn_local(rx.for_each(move |s| {
			match callback.call1(&callback, &JsValue::from_str(&s)) {
				Ok(_) => Ok(()),
				Err(_) => Err(()),
			}
		}).then(move |v| {
			// We need to keep `rpc_session` alive.
			debug!("RPC subscription has ended");
			drop(rpc_session);
			v
		}));
	}
}
