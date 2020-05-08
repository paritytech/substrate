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
use sc_network::config::TransportConfig;
use sc_service::{
	AbstractService, RpcSession, Role, Configuration,
	config::{DatabaseConfig, KeystoreConfig, NetworkConfiguration},
	GenericChainSpec, RuntimeGenesis
};
use wasm_bindgen::prelude::*;
use futures::{prelude::*, channel::{oneshot, mpsc}, future::{poll_fn, ok}, compat::*};
use std::task::Poll;
use std::pin::Pin;
use sc_chain_spec::Extension;
use libp2p_wasm_ext::{ExtTransport, ffi};

pub use console_error_panic_hook::set_once as set_console_error_panic_hook;
pub use console_log::init_with_level as init_console_log;

/// Create a service configuration from a chain spec.
///
/// This configuration contains good defaults for a browser light client.
pub async fn browser_configuration<G, E>(chain_spec: GenericChainSpec<G, E>)
	-> Result<Configuration, Box<dyn std::error::Error>>
where
	G: RuntimeGenesis + 'static,
	E: Extension + 'static + Send,
{
	let name = chain_spec.name().to_string();

	let transport = ExtTransport::new(ffi::websocket_transport());
	let mut network = NetworkConfiguration::new(
		format!("{} (Browser)", name),
		"unknown",
		Default::default(),
		None,
	);
	network.boot_nodes = chain_spec.boot_nodes().to_vec();
	network.transport = TransportConfig::Normal {
		wasm_external_transport: Some(transport.clone()),
		allow_private_ipv4: true,
		enable_mdns: false,
		use_yamux_flow_control: true,
	};

	let config = Configuration {
		network,
		telemetry_endpoints: chain_spec.telemetry_endpoints().clone(),
		chain_spec: Box::new(chain_spec),
		task_executor: Arc::new(move |fut, _| wasm_bindgen_futures::spawn_local(fut)),
		telemetry_external_transport: Some(transport),
		role: Role::Light,
		database: {
			info!("Opening Indexed DB database '{}'...", name);
			let db = kvdb_web::Database::open(name, 10).await?;

			DatabaseConfig::Custom(sp_database::as_database(db))
		},
		keystore: KeystoreConfig::InMemory,
		default_heap_pages: Default::default(),
		dev_key_seed: Default::default(),
		disable_grandpa: Default::default(),
		execution_strategies: Default::default(),
		force_authoring: Default::default(),
		impl_name: "parity-substrate",
		impl_version: "0.0.0",
		offchain_worker: Default::default(),
		prometheus_config: Default::default(),
		pruning: Default::default(),
		rpc_cors: Default::default(),
		rpc_http: Default::default(),
		rpc_ws: Default::default(),
		rpc_ws_max_connections: Default::default(),
		rpc_methods: Default::default(),
		state_cache_child_ratio: Default::default(),
		state_cache_size: Default::default(),
		tracing_receiver: Default::default(),
		tracing_targets: Default::default(),
		transaction_pool: Default::default(),
		wasm_method: Default::default(),
		max_runtime_instances: 8,
		announce_block: true,
	};

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
	// Spawn informant
	wasm_bindgen_futures::spawn_local(
		sc_informant::build(&service, sc_informant::OutputFormat::Plain).map(drop)
	);

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
