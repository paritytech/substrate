// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

use parking_lot::RwLock;
use std::sync::Arc;

use sc_rpc::SubscriptionTaskExecutor;
use sp_runtime::traits::Block as BlockT;

use futures::{
	future,
	task::{Spawn, SpawnError},
	FutureExt, StreamExt,
};
use jsonrpsee::{
	core::{async_trait, Error as JsonRpseeError, RpcResult},
	proc_macros::rpc,
	SubscriptionSink,
};
use log::warn;

use beefy_gadget::notification::BeefySignedCommitmentStream;

mod notification;

#[derive(Debug, derive_more::Display, derive_more::From, thiserror::Error)]
/// Top-level error type for the RPC handler
pub enum Error {
	/// The BEEFY RPC endpoint is not ready.
	#[display(fmt = "BEEFY RPC endpoint not ready")]
	EndpointNotReady,
	/// The BEEFY RPC background task failed to spawn.
	#[display(fmt = "BEEFY RPC background task failed to spawn")]
	RpcTaskFailure(SpawnError),
}

/// The error codes returned by jsonrpc.
pub enum ErrorCode {
	/// Returned when BEEFY RPC endpoint is not ready.
	NotReady = 1,
	/// Returned on BEEFY RPC background task failure.
	TaskFailure = 2,
}

/// Provides RPC methods for interacting with BEEFY.
#[rpc(client, server, namespace = "beefy")]
pub trait BeefyApi<Notification, Hash> {
	/// Returns the block most recently finalized by BEEFY, alongside side its justification.
	#[subscription(
		name = "subscribeJustifications" => "justifications",
		item = Notification,
	)]
	fn subscribe_justifications(&self) -> RpcResult<()>;

	/// Returns hash of the latest BEEFY finalized block as seen by this client.
	///
	/// The latest BEEFY block might not be available if the BEEFY gadget is not running
	/// in the network or if the client is still initializing or syncing with the network.
	/// In such case an error would be returned.
	#[method(name = "getFinalizedHead")]
	async fn latest_finalized(&self) -> RpcResult<Hash>;
}

/// Implements the BeefyApi RPC trait for interacting with BEEFY.
pub struct BeefyRpcHandler<Block: BlockT> {
	signed_commitment_stream: BeefySignedCommitmentStream<Block>,
	executor: SubscriptionTaskExecutor,
	beefy_best_block: Arc<RwLock<Option<Block::Hash>>>,
}

impl<Block> BeefyRpcHandler<Block>
where
	Block: BlockT,
{
	/// Creates a new BeefyRpcHandler instance.
	pub fn new(
		signed_commitment_stream: BeefySignedCommitmentStream<Block>,
		executor: SubscriptionTaskExecutor,
	) -> Self {
		let beefy_best_block = Arc::new(RwLock::new(None));
		Self { signed_commitment_stream, beefy_best_block, executor }
	}
}

#[async_trait]
impl<Block> BeefyApiServer<notification::EncodedSignedCommitment, Block::Hash>
	for BeefyRpcHandler<Block>
where
	Block: BlockT,
{
	fn subscribe_justifications(&self, mut sink: SubscriptionSink) -> RpcResult<()> {
		fn log_err(err: JsonRpseeError) -> bool {
			log::debug!(
				"Could not send data to beefy_justifications subscription. Error: {:?}",
				err
			);
			false
		}

		let stream = self
			.signed_commitment_stream
			.subscribe()
			.map(|sc| notification::EncodedSignedCommitment::new::<Block>(sc));

		let fut = async move {
			stream
				.take_while(|sc| future::ready(sink.send(sc).map_or_else(log_err, |_| true)))
				.for_each(|_| future::ready(()))
				.await
		}
		.boxed();

		self.executor
			.spawn_obj(fut.into())
			.map_err(|e| JsonRpseeError::to_call_error(e))
	}

	async fn latest_finalized(&self) -> RpcResult<Block::Hash> {
		self.beefy_best_block
			.read()
			.as_ref()
			.cloned()
			.ok_or(Error::EndpointNotReady)
			.map_err(|e| JsonRpseeError::to_call_error(e))
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use beefy_gadget::notification::{BeefySignedCommitment, BeefySignedCommitmentSender};
	use beefy_primitives::{known_payload_ids, Payload};
	use codec::{Decode, Encode};
	use jsonrpsee::{types::EmptyParams, RpcModule};
	use substrate_test_runtime_client::runtime::Block;

	fn setup_io_handler() -> (RpcModule<BeefyRpcHandler<Block>>, BeefySignedCommitmentSender<Block>)
	{
		let (commitment_sender, commitment_stream) =
			BeefySignedCommitmentStream::<Block>::channel();

		(
			BeefyRpcHandler::new(commitment_stream, sc_rpc::SubscriptionTaskExecutor::default())
				.into_rpc(),
			commitment_sender,
		)
	}

	#[tokio::test]
	async fn uninitialized_rpc_handler() {
		let (rpc, _) = setup_io_handler();
		let request = r#"{"jsonrpc":"2.0","method":"beefy_getFinalizedHead","params":[],"id":1}"#;
		let expected_response = r#"{"jsonrpc":"2.0","error":{"code":-32000,"message":"BEEFY RPC endpoint not ready"},"id":1}"#.to_string();
		let (result, _) = rpc.raw_json_request(&request).await.unwrap();

		assert_eq!(expected_response, result,);
	}

	// TODO: (dp)
	#[tokio::test]
	async fn latest_finalized_rpc() {
	}

	#[tokio::test]
	async fn subscribe_and_unsubscribe_to_justifications() {
		let (rpc, _) = setup_io_handler();

		// Subscribe call.
		let sub = rpc
			.subscribe("beefy_subscribeJustifications", EmptyParams::new())
			.await
			.unwrap();

		let ser_id = serde_json::to_string(sub.subscription_id()).unwrap();

		// Unsubscribe
		let unsub_req = format!(
			"{{\"jsonrpc\":\"2.0\",\"method\":\"beefy_unsubscribeJustifications\",\"params\":[{}],\"id\":1}}",
			ser_id
		);
		let (response, _) = rpc.raw_json_request(&unsub_req).await.unwrap();

		assert_eq!(response, r#"{"jsonrpc":"2.0","result":"Unsubscribed","id":1}"#);

		// Unsubscribe again and fail
		let (response, _) = rpc.raw_json_request(&unsub_req).await.unwrap();
		let expected = format!(
			r#"{{"jsonrpc":"2.0","error":{{"code":-32002,"message":"Server error","data":"Invalid subscription ID={}"}},"id":1}}"#,
			ser_id
		);

		assert_eq!(response, expected);
	}

	#[tokio::test]
	async fn subscribe_and_unsubscribe_with_wrong_id() {
		let (rpc, _) = setup_io_handler();
		// Subscribe call.
		let _sub = rpc
			.subscribe("beefy_subscribeJustifications", EmptyParams::new())
			.await
			.unwrap();

		// Unsubscribe with wrong ID
		let (response, _) = rpc
			.raw_json_request(
				r#"{"jsonrpc":"2.0","method":"beefy_unsubscribeJustifications","params":["FOO"],"id":1}"#,
			)
			.await
			.unwrap();
		let expected = r#"{"jsonrpc":"2.0","error":{"code":-32002,"message":"Server error","data":"Invalid subscription ID=\"FOO\""},"id":1}"#;

		assert_eq!(response, expected);
	}

	fn create_commitment() -> BeefySignedCommitment<Block> {
		let payload = Payload::new(known_payload_ids::MMR_ROOT_ID, "Hello World!".encode());
		BeefySignedCommitment::<Block> {
			commitment: beefy_primitives::Commitment {
				payload,
				block_number: 5,
				validator_set_id: 0,
			},
			signatures: vec![],
		}
	}

	#[tokio::test]
	async fn subscribe_and_listen_to_one_justification() {
		let (rpc, commitment_sender) = setup_io_handler();

		// Subscribe
		let mut sub = rpc
			.subscribe("beefy_subscribeJustifications", EmptyParams::new())
			.await
			.unwrap();

		// Notify with commitment
		let commitment = create_commitment();
		let r: Result<(), ()> = commitment_sender.notify(|| Ok(commitment.clone()));
		r.unwrap();

		// Inspect what we received
		let (bytes, recv_sub_id) = sub.next::<sp_core::Bytes>().await.unwrap().unwrap();
		let recv_commitment: BeefySignedCommitment<Block> =
			Decode::decode(&mut &bytes[..]).unwrap();
		assert_eq!(&recv_sub_id, sub.subscription_id());
		assert_eq!(recv_commitment, commitment);
	}
}
