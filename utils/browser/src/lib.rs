// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

use futures01::sync::mpsc as mpsc01;
use log::{debug, info};
use std::sync::Arc;
use service::{
	AbstractService, RpcSession, Roles, Configuration, config::{DatabaseConfig, KeystoreConfig},
	ChainSpec, RuntimeGenesis
};
use wasm_bindgen::prelude::*;
use futures::{prelude::*, channel::{oneshot, mpsc}, future::{poll_fn, ok}, compat::*};
use std::task::Poll;
use std::pin::Pin;
use chain_spec::Extension;

pub use libp2p::wasm_ext::{ExtTransport, ffi::Transport};
pub use console_error_panic_hook::set_once as set_console_error_panic_hook;
pub use console_log::init_with_level as init_console_log;

/// Create a service configuration from a chain spec and the websocket transport.
///
/// This configuration contains good defaults for a browser light client.
pub async fn browser_configuration<C, G, E>(
	transport: Transport,
	chain_spec: ChainSpec<G, E>,
) -> Result<Configuration<C, G, E>, Box<dyn std::error::Error>>
where
	C: Default,
	G: RuntimeGenesis,
	E: Extension,
{
	let name = chain_spec.name().to_string();

	let transport = ExtTransport::new(transport);
	let mut config = Configuration::default_with_spec_and_base_path(chain_spec, None);
	config.network.transport = network::config::TransportConfig::Normal {
		wasm_external_transport: Some(transport.clone()),
		allow_private_ipv4: true,
		enable_mdns: false,
	};
	config.tasks_executor = Some(Box::new(move |fut| {
		wasm_bindgen_futures::spawn_local(fut)
	}));
	config.telemetry_external_transport = Some(transport);
	config.roles = Roles::LIGHT;
	config.name = format!("{} (Browser)", name);
	config.database = {
		info!("Opening Indexed DB database '{}'...", name);
		let db = kvdb_web::Database::open(name, 10)
			.await?;
		DatabaseConfig::Custom(Arc::new(db))
	};
	config.keystore = KeystoreConfig::InMemory;

	Ok(config)
}

/// A running client.
#[wasm_bindgen]
pub struct Client {
	rpc_send_tx: mpsc::UnboundedSender<RpcMessage>,
}

struct RpcMessage {
	rpc_json: String,
	session: RpcSession,
	send_back: oneshot::Sender<Pin<Box<dyn futures::Future<Output = Option<String>> + Send>>>,
}

/// Create a Client object that connects to a service.
pub fn start_client(mut service: impl AbstractService) -> Client {
	// We dispatch a background task responsible for processing the service.
	//
	// The main action performed by the code below consists in polling the service with
	// `service.poll()`.
	// The rest consists in handling RPC requests.
	let (rpc_send_tx, mut rpc_send_rx) = mpsc::unbounded::<RpcMessage>();
	wasm_bindgen_futures::spawn_local(poll_fn(move |cx| {
		loop {
			match Pin::new(&mut rpc_send_rx).poll_next(cx) {
				Poll::Ready(Some(message)) => {
					let fut = service
						.rpc_query(&message.session, &message.rpc_json)
						.boxed();
					let _ = message.send_back.send(fut);
				},
				Poll::Pending => break,
				Poll::Ready(None) => return Poll::Ready(()),
			}
		}

		Pin::new(&mut service)
			.poll(cx)
			.map(drop)
	}));

	Client {
		rpc_send_tx,
	}
}

#[wasm_bindgen]
impl Client {
	/// Allows starting an RPC request. Returns a `Promise` containing the result of that request.
	#[wasm_bindgen(js_name = "rpcSend")]
	pub fn rpc_send(&mut self, rpc: &str) -> js_sys::Promise {
		let rpc_session = RpcSession::new(mpsc01::channel(1).0);
		let (tx, rx) = oneshot::channel();
		let _ = self.rpc_send_tx.unbounded_send(RpcMessage {
			rpc_json: rpc.to_owned(),
			session: rpc_session,
			send_back: tx,
		});
		wasm_bindgen_futures::future_to_promise(async {
			match rx.await {
				Ok(fut) => {
					fut.await
						.map(|s| JsValue::from_str(&s))
						.ok_or_else(|| JsValue::NULL)
				},
				Err(_) => Err(JsValue::NULL)
			}
		})
	}

	/// Subscribes to an RPC pubsub endpoint.
	#[wasm_bindgen(js_name = "rpcSubscribe")]
	pub fn rpc_subscribe(&mut self, rpc: &str, callback: js_sys::Function) {
		let (tx, rx) = mpsc01::channel(4);
		let rpc_session = RpcSession::new(tx);
		let (fut_tx, fut_rx) = oneshot::channel();
		let _ = self.rpc_send_tx.unbounded_send(RpcMessage {
			rpc_json: rpc.to_owned(),
			session: rpc_session.clone(),
			send_back: fut_tx,
		});
		wasm_bindgen_futures::spawn_local(async {
			if let Ok(fut) = fut_rx.await {
				fut.await;
			}
		});

		wasm_bindgen_futures::spawn_local(async move {
			let _ = rx.compat()
				.try_for_each(|s| {
					let _ = callback.call1(&callback, &JsValue::from_str(&s));
					ok(())
				})
				.await;

			// We need to keep `rpc_session` alive.
			debug!("RPC subscription has ended");
			drop(rpc_session);
		});
	}
}
