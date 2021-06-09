// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Substrate's client telemetry is a part of substrate that allows ingesting telemetry data
//! with for example [Polkadot telemetry](https://github.com/paritytech/substrate-telemetry).
//!
//! It works using Tokio's [tracing](https://github.com/tokio-rs/tracing/) library. The telemetry
//! information uses tracing's logging to report the telemetry data which is then retrieved by a
//! tracing `Layer`. This layer will then send the data through an asynchronous channel to a
//! background task called [`TelemetryWorker`] which will send the information to the configured
//! remote telemetry servers.
//!
//! If multiple substrate nodes are running in the same process, it uses a `tracing::Span` to
//! identify which substrate node is reporting the telemetry. Every task spawned using sc-service's
//! `TaskManager` automatically inherit this span.
//!
//! Substrate's nodes initialize/register with the [`TelemetryWorker`] using a [`TelemetryWorkerHandle`].
//! This handle can be cloned and passed around. It uses an asynchronous channel to communicate with
//! the running [`TelemetryWorker`] dedicated to registration. Registering can happen at any point
//! in time during the process execution.

#![warn(missing_docs)]

use futures::{channel::mpsc, prelude::*};
use libp2p::Multiaddr;
use log::{error, warn};
use parking_lot::Mutex;
use serde::Serialize;
use std::collections::HashMap;
use std::sync::{atomic, Arc};

pub use libp2p::wasm_ext::ExtTransport;
pub use log;
pub use serde_json;

mod endpoints;
mod error;
mod node;
mod transport;

pub use endpoints::*;
pub use error::*;
use node::*;
use transport::*;

/// Substrate DEBUG log level.
pub const SUBSTRATE_DEBUG: VerbosityLevel = 9;
/// Substrate INFO log level.
pub const SUBSTRATE_INFO: VerbosityLevel = 0;

/// Consensus TRACE log level.
pub const CONSENSUS_TRACE: VerbosityLevel = 9;
/// Consensus DEBUG log level.
pub const CONSENSUS_DEBUG: VerbosityLevel = 5;
/// Consensus WARN log level.
pub const CONSENSUS_WARN: VerbosityLevel = 4;
/// Consensus INFO log level.
pub const CONSENSUS_INFO: VerbosityLevel = 1;

/// Telemetry message verbosity.
pub type VerbosityLevel = u8;

pub(crate) type Id = u64;
pub(crate) type TelemetryPayload = serde_json::Map<String, serde_json::Value>;
pub(crate) type TelemetryMessage = (Id, VerbosityLevel, TelemetryPayload);

/// Message sent when the connection (re-)establishes.
#[derive(Debug, Serialize)]
pub struct ConnectionMessage {
	/// Node's name.
	pub name: String,
	/// Node's implementation.
	pub implementation: String,
	/// Node's version.
	pub version: String,
	/// Node's configuration.
	pub config: String,
	/// Node's chain.
	pub chain: String,
	/// Node's genesis hash.
	pub genesis_hash: String,
	/// Node is an authority.
	pub authority: bool,
	/// Node's startup time.
	pub startup_time: String,
	/// Node's network ID.
	pub network_id: String,
}

/// Telemetry worker.
///
/// It should run as a background task using the [`TelemetryWorker::run`] method. This method
/// will consume the object and any further attempts of initializing a new telemetry through its
/// handle will fail (without being fatal).
#[derive(Debug)]
pub struct TelemetryWorker {
	message_receiver: mpsc::Receiver<TelemetryMessage>,
	message_sender: mpsc::Sender<TelemetryMessage>,
	register_receiver: mpsc::UnboundedReceiver<Register>,
	register_sender: mpsc::UnboundedSender<Register>,
	id_counter: Arc<atomic::AtomicU64>,
	transport: WsTrans,
}

impl TelemetryWorker {
	/// Instantiate a new [`TelemetryWorker`] which can run in background.
	///
	/// Only one is needed per process.
	pub fn new(buffer_size: usize) -> Result<Self> {
		Self::with_transport(buffer_size, None)
	}

	/// Instantiate a new [`TelemetryWorker`] with the given [`ExtTransport`]
	/// which can run in background.
	///
	/// Only one is needed per process.
	pub fn with_transport(buffer_size: usize, transport: Option<ExtTransport>) -> Result<Self> {
		let transport = initialize_transport(transport)?;
		let (message_sender, message_receiver) = mpsc::channel(buffer_size);
		let (register_sender, register_receiver) = mpsc::unbounded();

		Ok(Self {
			message_receiver,
			message_sender,
			register_receiver,
			register_sender,
			id_counter: Arc::new(atomic::AtomicU64::new(1)),
			transport,
		})
	}

	/// Get a new [`TelemetryWorkerHandle`].
	///
	/// This is used when you want to register with the [`TelemetryWorker`].
	pub fn handle(&self) -> TelemetryWorkerHandle {
		TelemetryWorkerHandle {
			message_sender: self.message_sender.clone(),
			register_sender: self.register_sender.clone(),
			id_counter: self.id_counter.clone(),
		}
	}

	/// Run the telemetry worker.
	///
	/// This should be run in a background task.
	pub async fn run(mut self) {
		let mut node_map: HashMap<Id, Vec<(VerbosityLevel, Multiaddr)>> = HashMap::new();
		let mut node_pool: HashMap<Multiaddr, _> = HashMap::new();
		let mut pending_connection_notifications: Vec<_> = Vec::new();

		loop {
			futures::select! {
				message = self.message_receiver.next() => Self::process_message(
					message,
					&mut node_pool,
					&node_map,
				).await,
				init_payload = self.register_receiver.next() => Self::process_register(
					init_payload,
					&mut node_pool,
					&mut node_map,
					&mut pending_connection_notifications,
					self.transport.clone(),
				).await,
			}
		}
	}

	async fn process_register(
		input: Option<Register>,
		node_pool: &mut HashMap<Multiaddr, Node<WsTrans>>,
		node_map: &mut HashMap<Id, Vec<(VerbosityLevel, Multiaddr)>>,
		pending_connection_notifications: &mut Vec<(Multiaddr, ConnectionNotifierSender)>,
		transport: WsTrans,
	) {
		let input = input.expect("the stream is never closed; qed");

		match input {
			Register::Telemetry {
				id,
				endpoints,
				connection_message,
			} => {
				let endpoints = endpoints.0;

				let connection_message = match serde_json::to_value(&connection_message) {
					Ok(serde_json::Value::Object(mut value)) => {
						value.insert("msg".into(), "system.connected".into());
						let mut obj = serde_json::Map::new();
						obj.insert("id".to_string(), id.into());
						obj.insert("payload".to_string(), value.into());
						Some(obj)
					}
					Ok(_) => {
						unreachable!("ConnectionMessage always serialize to an object; qed")
					}
					Err(err) => {
						log::error!(
							target: "telemetry",
							"Could not serialize connection message: {}",
							err,
						);
						None
					}
				};

				for (addr, verbosity) in endpoints {
					log::trace!(
						target: "telemetry",
						"Initializing telemetry for: {:?}",
						addr,
					);
					node_map
						.entry(id.clone())
						.or_default()
						.push((verbosity, addr.clone()));

					let node = node_pool.entry(addr.clone()).or_insert_with(|| {
						Node::new(transport.clone(), addr.clone(), Vec::new(), Vec::new())
					});

					node.connection_messages.extend(connection_message.clone());

					pending_connection_notifications.retain(|(addr_b, connection_message)| {
						if *addr_b == addr {
							node.telemetry_connection_notifier
								.push(connection_message.clone());
							false
						} else {
							true
						}
					});
				}
			}
			Register::Notifier {
				addresses,
				connection_notifier,
			} => {
				for addr in addresses {
					// If the Node has been initialized, we directly push the connection_notifier.
					// Otherwise we push it to a queue that will be consumed when the connection
					// initializes, thus ensuring that the connection notifier will be sent to the
					// Node when it becomes available.
					if let Some(node) = node_pool.get_mut(&addr) {
						node.telemetry_connection_notifier
							.push(connection_notifier.clone());
					} else {
						pending_connection_notifications.push((addr, connection_notifier.clone()));
					}
				}
			}
		}
	}

	// dispatch messages to the telemetry nodes
	async fn process_message(
		input: Option<TelemetryMessage>,
		node_pool: &mut HashMap<Multiaddr, Node<WsTrans>>,
		node_map: &HashMap<Id, Vec<(VerbosityLevel, Multiaddr)>>,
	) {
		let (id, verbosity, payload) = input.expect("the stream is never closed; qed");

		let ts = chrono::Local::now().to_rfc3339().to_string();
		let mut message = serde_json::Map::new();
		message.insert("id".into(), id.into());
		message.insert("ts".into(), ts.into());
		message.insert("payload".into(), payload.into());

		let nodes = if let Some(nodes) = node_map.get(&id) {
			nodes
		} else {
			// This is a normal error because the telemetry ID exists before the telemetry is
			// initialized.
			log::trace!(
				target: "telemetry",
				"Received telemetry log for unknown id ({:?}): {}",
				id,
				serde_json::to_string(&message)
					.unwrap_or_else(|err| format!(
						"could not be serialized ({}): {:?}",
						err,
						message,
					)),
			);
			return;
		};

		for (node_max_verbosity, addr) in nodes {
			if verbosity > *node_max_verbosity {
				continue;
			}

			if let Some(node) = node_pool.get_mut(&addr) {
				let _ = node.send(message.clone()).await;
			} else {
				log::debug!(
					target: "telemetry",
					"Received message for unknown node ({}). This is a bug. \
					Message sent: {}",
					addr,
					serde_json::to_string(&message)
						.unwrap_or_else(|err| format!(
							"could not be serialized ({}): {:?}",
							err,
							message,
						)),
				);
			}
		}
	}
}

/// Handle to the [`TelemetryWorker`] thats allows initializing the telemetry for a Substrate node.
#[derive(Debug, Clone)]
pub struct TelemetryWorkerHandle {
	message_sender: mpsc::Sender<TelemetryMessage>,
	register_sender: mpsc::UnboundedSender<Register>,
	id_counter: Arc<atomic::AtomicU64>,
}

impl TelemetryWorkerHandle {
	/// Instantiate a new [`Telemetry`] object.
	pub fn new_telemetry(&mut self, endpoints: TelemetryEndpoints) -> Telemetry {
		let addresses = endpoints.0.iter().map(|(addr, _)| addr.clone()).collect();

		Telemetry {
			message_sender: self.message_sender.clone(),
			register_sender: self.register_sender.clone(),
			id: self.id_counter.fetch_add(1, atomic::Ordering::Relaxed),
			connection_notifier: TelemetryConnectionNotifier {
				register_sender: self.register_sender.clone(),
				addresses,
			},
			endpoints: Some(endpoints),
		}
	}
}

/// A telemetry instance that can be used to send telemetry messages.
#[derive(Debug)]
pub struct Telemetry {
	message_sender: mpsc::Sender<TelemetryMessage>,
	register_sender: mpsc::UnboundedSender<Register>,
	id: Id,
	connection_notifier: TelemetryConnectionNotifier,
	endpoints: Option<TelemetryEndpoints>,
}

impl Telemetry {
	/// Initialize the telemetry with the endpoints provided in argument for the current substrate
	/// node.
	///
	/// This method must be called during the substrate node initialization.
	///
	/// The `endpoints` argument is a collection of telemetry WebSocket servers with a corresponding
	/// verbosity level.
	///
	/// The `connection_message` argument is a JSON object that is sent every time the connection
	/// (re-)establishes.
	pub fn start_telemetry(&mut self, connection_message: ConnectionMessage) -> Result<()> {
		let endpoints = self.endpoints.take().ok_or_else(|| Error::TelemetryAlreadyInitialized)?;

		self.register_sender
			.unbounded_send(Register::Telemetry {
				id: self.id,
				endpoints,
				connection_message,
			})
			.map_err(|_| Error::TelemetryWorkerDropped)
	}

	/// Make a new cloneable handle to this [`Telemetry`]. This is used for reporting telemetries.
	pub fn handle(&self) -> TelemetryHandle {
		TelemetryHandle {
			message_sender: Arc::new(Mutex::new(self.message_sender.clone())),
			id: self.id,
			connection_notifier: self.connection_notifier.clone(),
		}
	}
}

/// Handle to a [`Telemetry`].
///
/// Used to report telemetry messages.
#[derive(Debug, Clone)]
pub struct TelemetryHandle {
	message_sender: Arc<Mutex<mpsc::Sender<TelemetryMessage>>>,
	id: Id,
	connection_notifier: TelemetryConnectionNotifier,
}

impl TelemetryHandle {
	/// Send telemetry messages.
	pub fn send_telemetry(&self, verbosity: VerbosityLevel, payload: TelemetryPayload) {
		match self
			.message_sender
			.lock()
			.try_send((self.id, verbosity, payload))
		{
			Ok(()) => {}
			Err(err) if err.is_full() => log::trace!(
				target: "telemetry",
				"Telemetry channel full.",
			),
			Err(_) => log::trace!(
				target: "telemetry",
				"Telemetry channel closed.",
			),
		}
	}

	/// Get event stream for telemetry connection established events.
	///
	/// This function will return an error if the telemetry has already been started by
	/// [`Telemetry::start_telemetry`].
	pub fn on_connect_stream(&self) -> ConnectionNotifierReceiver {
		self.connection_notifier.on_connect_stream()
	}
}

/// Used to create a stream of events with only one event: when a telemetry connection
/// (re-)establishes.
#[derive(Clone, Debug)]
pub struct TelemetryConnectionNotifier {
	register_sender: mpsc::UnboundedSender<Register>,
	addresses: Vec<Multiaddr>,
}

impl TelemetryConnectionNotifier {
	fn on_connect_stream(&self) -> ConnectionNotifierReceiver {
		let (message_sender, message_receiver) = connection_notifier_channel();
		if let Err(err) = self.register_sender.unbounded_send(Register::Notifier {
			addresses: self.addresses.clone(),
			connection_notifier: message_sender,
		}) {
			error!(
				target: "telemetry",
				"Could not create a telemetry connection notifier: \
				the telemetry is probably already running: {}",
				err,
			);
		}
		message_receiver
	}
}

#[derive(Debug)]
enum Register {
	Telemetry {
		id: Id,
		endpoints: TelemetryEndpoints,
		connection_message: ConnectionMessage,
	},
	Notifier {
		addresses: Vec<Multiaddr>,
		connection_notifier: ConnectionNotifierSender,
	},
}

/// Report a telemetry.
///
/// Translates to [`tracing::info`], but contains an additional verbosity parameter which the log
/// record is tagged with. Additionally the verbosity parameter is added to the record as a
/// key-value pair.
///
/// # Example
///
/// ```no_run
/// # use sc_telemetry::*;
/// # let authority_id = 42_u64;
/// # let set_id = (43_u64, 44_u64);
/// # let authorities = vec![45_u64];
/// # let telemetry: Option<TelemetryHandle> = None;
/// telemetry!(
///     telemetry;      // an `Option<TelemetryHandle>`
///     CONSENSUS_INFO;
///     "afg.authority_set";
///     "authority_id" => authority_id.to_string(),
///     "authority_set_id" => ?set_id,
///     "authorities" => authorities,
/// );
/// ```
#[macro_export(local_inner_macros)]
macro_rules! telemetry {
	( $telemetry:expr; $verbosity:expr; $msg:expr; $( $t:tt )* ) => {{
		if let Some(telemetry) = $telemetry.as_ref() {
			let verbosity: $crate::VerbosityLevel = $verbosity;
			match format_fields_to_json!($($t)*) {
				Err(err) => {
					$crate::log::debug!(
						target: "telemetry",
						"Could not serialize value for telemetry: {}",
						err,
					);
				},
				Ok(mut json) => {
					json.insert("msg".into(), $msg.into());
					telemetry.send_telemetry(verbosity, json);
				},
			}
		}
	}};
}

#[macro_export(local_inner_macros)]
#[doc(hidden)]
macro_rules! format_fields_to_json {
	( $k:literal => $v:expr $(,)? $(, $($t:tt)+ )? ) => {{
		$crate::serde_json::to_value(&$v)
			.map(|value| {
				let mut map = $crate::serde_json::Map::new();
				map.insert($k.into(), value);
				map
			})
			$(
				.and_then(|mut prev_map| {
					format_fields_to_json!($($t)*)
						.map(move |mut other_map| {
							prev_map.append(&mut other_map);
							prev_map
						})
				})
			)*
	}};
	( $k:literal => ? $v:expr $(,)? $(, $($t:tt)+ )? ) => {{
		let mut map = $crate::serde_json::Map::new();
		map.insert($k.into(), std::format!("{:?}", &$v).into());
		$crate::serde_json::Result::Ok(map)
		$(
			.and_then(|mut prev_map| {
				format_fields_to_json!($($t)*)
					.map(move |mut other_map| {
						prev_map.append(&mut other_map);
						prev_map
					})
			})
		)*
	}};
}
