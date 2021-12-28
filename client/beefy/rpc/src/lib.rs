// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

//! RPC API for BEEFY.

#![warn(missing_docs)]

use parking_lot::Mutex;
use std::sync::Arc;

use sp_runtime::traits::{Block as BlockT, NumberFor};

use futures::{FutureExt, SinkExt, StreamExt, TryFutureExt};
use jsonrpc_derive::rpc;
use jsonrpc_pubsub::{manager::SubscriptionManager, typed::Subscriber, SubscriptionId};
use log::warn;

use beefy_gadget::notification::{BSignedCommitment, BeefyNotificationStream};

mod notification;

type FutureResult<T> = jsonrpc_core::BoxFuture<Result<T, jsonrpc_core::Error>>;

#[derive(derive_more::Display, derive_more::From)]
/// Top-level error type for the RPC handler
pub enum Error {
	/// The BEEFY RPC endpoint is not ready.
	#[display(fmt = "BEEFY RPC endpoint not ready")]
	EndpointNotReady,
}

/// The error codes returned by jsonrpc.
pub enum ErrorCode {
	/// Returned when BEEFY RPC endpoint is not ready.
	NotReady = 1,
}

impl From<Error> for ErrorCode {
	fn from(error: Error) -> Self {
		match error {
			Error::EndpointNotReady => ErrorCode::NotReady,
		}
	}
}

impl From<Error> for jsonrpc_core::Error {
	fn from(error: Error) -> Self {
		let message = format!("{}", error);
		let code = ErrorCode::from(error);
		jsonrpc_core::Error {
			message,
			code: jsonrpc_core::ErrorCode::ServerError(code as i64),
			data: None,
		}
	}
}

/// Provides RPC methods for interacting with BEEFY.
#[rpc]
pub trait BeefyApi<Notification, Number> {
	/// RPC Metadata
	type Metadata;

	/// Returns the block most recently finalized by BEEFY, alongside side its justification.
	#[pubsub(
		subscription = "beefy_justifications",
		subscribe,
		name = "beefy_subscribeJustifications"
	)]
	fn subscribe_justifications(
		&self,
		metadata: Self::Metadata,
		subscriber: Subscriber<Notification>,
	);

	/// Unsubscribe from receiving notifications about recently finalized blocks.
	#[pubsub(
		subscription = "beefy_justifications",
		unsubscribe,
		name = "beefy_unsubscribeJustifications"
	)]
	fn unsubscribe_justifications(
		&self,
		metadata: Option<Self::Metadata>,
		id: SubscriptionId,
	) -> jsonrpc_core::Result<bool>;

	/// Returns the latest beefy finalized block as see by this client.
	#[rpc(name = "beefy_latestFinalized")]
	fn latest_finalized(&self) -> FutureResult<Number>;
}

/// Implements the BeefyApi RPC trait for interacting with BEEFY.
pub struct BeefyRpcHandler<Block: BlockT> {
	signed_commitment_stream: BeefyNotificationStream<BSignedCommitment<Block>>,
	beefy_best_block: Arc<Mutex<Option<NumberFor<Block>>>>,
	manager: SubscriptionManager,
}

impl<Block: BlockT> BeefyRpcHandler<Block> {
	/// Creates a new BeefyRpcHandler instance.
	pub fn new<E>(
		signed_commitment_stream: BeefyNotificationStream<BSignedCommitment<Block>>,
		best_block_stream: BeefyNotificationStream<NumberFor<Block>>,
		executor: E,
	) -> Self
	where
		E: futures::task::Spawn + Send + Sync + 'static,
	{
		let beefy_best_block = Arc::new(Mutex::new(None));

		let stream = best_block_stream.subscribe();
		let closure_clone = beefy_best_block.clone();
		let future = stream.for_each(move |best_beefy| {
			let async_clone = closure_clone.clone();
			async move {
				*async_clone.lock() = Some(best_beefy);
			}
		});

		if executor.spawn_obj(futures::task::FutureObj::new(Box::pin(future))).is_err() {
			log::error!("Failed to spawn best beefy RPC task");
		}

		let manager = SubscriptionManager::new(Arc::new(executor));
		Self { signed_commitment_stream, beefy_best_block, manager }
	}
}

impl<Block> BeefyApi<notification::EncodedSignedCommitment, NumberFor<Block>>
	for BeefyRpcHandler<Block>
where
	Block: BlockT,
{
	type Metadata = sc_rpc::Metadata;

	fn subscribe_justifications(
		&self,
		_metadata: Self::Metadata,
		subscriber: Subscriber<notification::EncodedSignedCommitment>,
	) {
		let stream = self
			.signed_commitment_stream
			.subscribe()
			.map(|x| Ok::<_, ()>(Ok(notification::EncodedSignedCommitment::new::<Block>(x))));

		self.manager.add(subscriber, |sink| {
			stream
				.forward(sink.sink_map_err(|e| warn!("Error sending notifications: {:?}", e)))
				.map(|_| ())
		});
	}

	fn unsubscribe_justifications(
		&self,
		_metadata: Option<Self::Metadata>,
		id: SubscriptionId,
	) -> jsonrpc_core::Result<bool> {
		Ok(self.manager.cancel(id))
	}

	fn latest_finalized(&self) -> FutureResult<NumberFor<Block>> {
		let result: Result<NumberFor<Block>, jsonrpc_core::Error> = self
			.beefy_best_block
			.lock()
			.as_ref()
			.cloned()
			.ok_or(Error::EndpointNotReady.into());
		let future = async move { result }.boxed();
		future.map_err(jsonrpc_core::Error::from).boxed()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use jsonrpc_core::{types::Params, Notification, Output};

	use beefy_gadget::notification::{BSignedCommitment, BeefyNotificationSender};
	use beefy_primitives::{known_payload_ids, Payload};
	use codec::{Decode, Encode};
	use substrate_test_runtime_client::runtime::Block;

	fn setup_io_handler() -> (
		jsonrpc_core::MetaIoHandler<sc_rpc::Metadata>,
		BeefyNotificationSender<BSignedCommitment<Block>>,
	) {
		let (_, stream) = BeefyNotificationStream::channel();
		setup_io_handler_with_best_block_stream(stream)
	}

	fn setup_io_handler_with_best_block_stream(
		best_block_stream: BeefyNotificationStream<NumberFor<Block>>,
	) -> (
		jsonrpc_core::MetaIoHandler<sc_rpc::Metadata>,
		BeefyNotificationSender<BSignedCommitment<Block>>,
	) {
		let (commitment_sender, commitment_stream) = BeefyNotificationStream::channel();

		let handler: BeefyRpcHandler<Block> = BeefyRpcHandler::new(
			commitment_stream,
			best_block_stream,
			sc_rpc::testing::TaskExecutor,
		);

		let mut io = jsonrpc_core::MetaIoHandler::default();
		io.extend_with(BeefyApi::to_delegate(handler));

		(io, commitment_sender)
	}

	fn setup_session() -> (sc_rpc::Metadata, futures::channel::mpsc::UnboundedReceiver<String>) {
		let (tx, rx) = futures::channel::mpsc::unbounded();
		let meta = sc_rpc::Metadata::new(tx);
		(meta, rx)
	}

	#[test]
	fn uninitialized_rpc_handler() {
		let (io, _) = setup_io_handler();

		let request = r#"{"jsonrpc":"2.0","method":"beefy_latestFinalized","params":[],"id":1}"#;
		let response = r#"{"jsonrpc":"2.0","error":{"code":1,"message":"BEEFY RPC endpoint not ready"},"id":1}"#;

		let meta = sc_rpc::Metadata::default();
		assert_eq!(Some(response.into()), io.handle_request_sync(request, meta));
	}

	#[test]
	fn latest_finalized_rpc() {
		let (sender, stream) = BeefyNotificationStream::channel();
		let (io, _) = setup_io_handler_with_best_block_stream(stream);

		// Send BeefyRpcHandler `beefy_best_block = 42`
		let num: NumberFor<Block> = 42u16.into();
		sender.notify(num);

		// Wait a bit so the message is picked up.
		std::thread::sleep(std::time::Duration::from_millis(200));

		// Verify RPC `beefy_latestFinalized` returns `42`
		let request = r#"{"jsonrpc":"2.0","method":"beefy_latestFinalized","params":[],"id":1}"#;
		let response = r#"{"jsonrpc":"2.0","result":42,"id":1}"#;
		let meta = sc_rpc::Metadata::default();
		assert_eq!(Some(response.into()), io.handle_request_sync(request, meta));
	}

	#[test]
	fn subscribe_and_unsubscribe_to_justifications() {
		let (io, _) = setup_io_handler();
		let (meta, _) = setup_session();

		// Subscribe
		let sub_request =
			r#"{"jsonrpc":"2.0","method":"beefy_subscribeJustifications","params":[],"id":1}"#;
		let resp = io.handle_request_sync(sub_request, meta.clone());
		let resp: Output = serde_json::from_str(&resp.unwrap()).unwrap();

		let sub_id = match resp {
			Output::Success(success) => success.result,
			_ => panic!(),
		};

		// Unsubscribe
		let unsub_req = format!(
			"{{\"jsonrpc\":\"2.0\",\"method\":\"beefy_unsubscribeJustifications\",\"params\":[{}],\"id\":1}}",
			sub_id
		);
		assert_eq!(
			io.handle_request_sync(&unsub_req, meta.clone()),
			Some(r#"{"jsonrpc":"2.0","result":true,"id":1}"#.into()),
		);

		// Unsubscribe again and fail
		assert_eq!(
			io.handle_request_sync(&unsub_req, meta),
			Some("{\"jsonrpc\":\"2.0\",\"error\":{\"code\":-32602,\"message\":\"Invalid subscription id.\"},\"id\":1}".into()),
		);
	}

	#[test]
	fn subscribe_and_unsubscribe_with_wrong_id() {
		let (io, _) = setup_io_handler();
		let (meta, _) = setup_session();

		// Subscribe
		let sub_request =
			r#"{"jsonrpc":"2.0","method":"beefy_subscribeJustifications","params":[],"id":1}"#;
		let resp = io.handle_request_sync(sub_request, meta.clone());
		let resp: Output = serde_json::from_str(&resp.unwrap()).unwrap();
		assert!(matches!(resp, Output::Success(_)));

		// Unsubscribe with wrong ID
		assert_eq!(
			io.handle_request_sync(
				r#"{"jsonrpc":"2.0","method":"beefy_unsubscribeJustifications","params":["FOO"],"id":1}"#,
				meta.clone()
			),
			Some("{\"jsonrpc\":\"2.0\",\"error\":{\"code\":-32602,\"message\":\"Invalid subscription id.\"},\"id\":1}".into())
		);
	}

	fn create_commitment() -> BSignedCommitment<Block> {
		let payload = Payload::new(known_payload_ids::MMR_ROOT_ID, "Hello World!".encode());
		BSignedCommitment::<Block> {
			commitment: beefy_primitives::Commitment {
				payload,
				block_number: 5,
				validator_set_id: 0,
			},
			signatures: vec![],
		}
	}

	#[test]
	fn subscribe_and_listen_to_one_justification() {
		let (io, commitment_sender) = setup_io_handler();
		let (meta, receiver) = setup_session();

		// Subscribe
		let sub_request =
			r#"{"jsonrpc":"2.0","method":"beefy_subscribeJustifications","params":[],"id":1}"#;

		let resp = io.handle_request_sync(sub_request, meta.clone());
		let mut resp: serde_json::Value = serde_json::from_str(&resp.unwrap()).unwrap();
		let sub_id: String = serde_json::from_value(resp["result"].take()).unwrap();

		// Notify with commitment
		let commitment = create_commitment();
		commitment_sender.notify(commitment.clone());

		// Inspect what we received
		let recv = futures::executor::block_on(receiver.take(1).collect::<Vec<_>>());
		let recv: Notification = serde_json::from_str(&recv[0]).unwrap();
		let mut json_map = match recv.params {
			Params::Map(json_map) => json_map,
			_ => panic!(),
		};

		let recv_sub_id: String = serde_json::from_value(json_map["subscription"].take()).unwrap();
		let recv_commitment: sp_core::Bytes =
			serde_json::from_value(json_map["result"].take()).unwrap();
		let recv_commitment: BSignedCommitment<Block> =
			Decode::decode(&mut &recv_commitment[..]).unwrap();

		assert_eq!(recv.method, "beefy_justifications");
		assert_eq!(recv_sub_id, sub_id);
		assert_eq!(recv_commitment, commitment);
	}
}
