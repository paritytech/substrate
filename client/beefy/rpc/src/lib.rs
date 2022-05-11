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

use futures::{task::SpawnError, FutureExt, StreamExt};
use jsonrpsee::{
	core::{async_trait, Error as JsonRpseeError, RpcResult},
	proc_macros::rpc,
	types::{error::CallError, ErrorObject},
	PendingSubscription,
};
use log::warn;

use beefy_gadget::notification::{BeefyBestBlockStream, BeefySignedCommitmentStream};

mod notification;

#[derive(Debug, thiserror::Error)]
/// Top-level error type for the RPC handler
pub enum Error {
	/// The BEEFY RPC endpoint is not ready.
	#[error("BEEFY RPC endpoint not ready")]
	EndpointNotReady,
	/// The BEEFY RPC background task failed to spawn.
	#[error("BEEFY RPC background task failed to spawn")]
	RpcTaskFailure(#[from] SpawnError),
}

/// The error codes returned by jsonrpc.
pub enum ErrorCode {
	/// Returned when BEEFY RPC endpoint is not ready.
	NotReady = 1,
	/// Returned on BEEFY RPC background task failure.
	TaskFailure = 2,
}

impl From<Error> for ErrorCode {
	fn from(error: Error) -> Self {
		match error {
			Error::EndpointNotReady => ErrorCode::NotReady,
			Error::RpcTaskFailure(_) => ErrorCode::TaskFailure,
		}
	}
}

impl From<Error> for JsonRpseeError {
	fn from(error: Error) -> Self {
		let message = error.to_string();
		let code = ErrorCode::from(error);
		JsonRpseeError::Call(CallError::Custom(ErrorObject::owned(
			code as i32,
			message,
			None::<()>,
		)))
	}
}

// Provides RPC methods for interacting with BEEFY.
#[rpc(client, server)]
pub trait BeefyApi<Notification, Hash> {
	/// Returns the block most recently finalized by BEEFY, alongside side its justification.
	#[subscription(
		name = "beefy_subscribeJustifications" => "beefy_justifications",
		unsubscribe = "beefy_unsubscribeJustifications",
		item = Notification,
	)]
	fn subscribe_justifications(&self);

	/// Returns hash of the latest BEEFY finalized block as seen by this client.
	///
	/// The latest BEEFY block might not be available if the BEEFY gadget is not running
	/// in the network or if the client is still initializing or syncing with the network.
	/// In such case an error would be returned.
	#[method(name = "beefy_getFinalizedHead")]
	async fn latest_finalized(&self) -> RpcResult<Hash>;
}

/// Implements the BeefyApi RPC trait for interacting with BEEFY.
pub struct BeefyRpcHandler<Block: BlockT> {
	signed_commitment_stream: BeefySignedCommitmentStream<Block>,
	beefy_best_block: Arc<RwLock<Option<Block::Hash>>>,
	executor: SubscriptionTaskExecutor,
}

impl<Block> BeefyRpcHandler<Block>
where
	Block: BlockT,
{
	/// Creates a new BeefyRpcHandler instance.
	pub fn new(
		signed_commitment_stream: BeefySignedCommitmentStream<Block>,
		best_block_stream: BeefyBestBlockStream<Block>,
		executor: SubscriptionTaskExecutor,
	) -> Result<Self, Error> {
		let beefy_best_block = Arc::new(RwLock::new(None));

		let stream = best_block_stream.subscribe();
		let closure_clone = beefy_best_block.clone();
		let future = stream.for_each(move |best_beefy| {
			let async_clone = closure_clone.clone();
			async move { *async_clone.write() = Some(best_beefy) }
		});

		executor.spawn("substrate-rpc-subscription", Some("rpc"), future.map(drop).boxed());
		Ok(Self { signed_commitment_stream, beefy_best_block, executor })
	}
}

#[async_trait]
impl<Block> BeefyApiServer<notification::EncodedSignedCommitment, Block::Hash>
	for BeefyRpcHandler<Block>
where
	Block: BlockT,
{
	fn subscribe_justifications(&self, pending: PendingSubscription) {
		let stream = self
			.signed_commitment_stream
			.subscribe()
			.map(|sc| notification::EncodedSignedCommitment::new::<Block>(sc));

		let fut = async move {
			if let Some(mut sink) = pending.accept() {
				sink.pipe_from_stream(stream).await;
			}
		}
		.boxed();

		self.executor
			.spawn("substrate-rpc-subscription", Some("rpc"), fut.map(drop).boxed());
	}

	async fn latest_finalized(&self) -> RpcResult<Block::Hash> {
		self.beefy_best_block
			.read()
			.as_ref()
			.cloned()
			.ok_or(Error::EndpointNotReady)
			.map_err(Into::into)
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use beefy_gadget::notification::{
		BeefyBestBlockStream, BeefySignedCommitment, BeefySignedCommitmentSender,
	};
	use beefy_primitives::{known_payload_ids, Payload};
	use codec::{Decode, Encode};
	use jsonrpsee::{types::EmptyParams, RpcModule};
	use sp_runtime::traits::{BlakeTwo256, Hash};
	use substrate_test_runtime_client::runtime::Block;

	fn setup_io_handler() -> (RpcModule<BeefyRpcHandler<Block>>, BeefySignedCommitmentSender<Block>)
	{
		let (_, stream) = BeefyBestBlockStream::<Block>::channel();
		setup_io_handler_with_best_block_stream(stream)
	}

	fn setup_io_handler_with_best_block_stream(
		best_block_stream: BeefyBestBlockStream<Block>,
	) -> (RpcModule<BeefyRpcHandler<Block>>, BeefySignedCommitmentSender<Block>) {
		let (commitment_sender, commitment_stream) =
			BeefySignedCommitmentStream::<Block>::channel();

		let handler = BeefyRpcHandler::new(
			commitment_stream,
			best_block_stream,
			sc_rpc::testing::test_executor(),
		)
		.expect("Setting up the BEEFY RPC handler works");

		(handler.into_rpc(), commitment_sender)
	}

	#[tokio::test]
	async fn uninitialized_rpc_handler() {
		let (rpc, _) = setup_io_handler();
		let request = r#"{"jsonrpc":"2.0","method":"beefy_getFinalizedHead","params":[],"id":1}"#;
		let expected_response = r#"{"jsonrpc":"2.0","error":{"code":1,"message":"BEEFY RPC endpoint not ready"},"id":1}"#.to_string();
		let (result, _) = rpc.raw_json_request(&request).await.unwrap();

		assert_eq!(expected_response, result,);
	}

	#[tokio::test]
	async fn latest_finalized_rpc() {
		let (sender, stream) = BeefyBestBlockStream::<Block>::channel();
		let (io, _) = setup_io_handler_with_best_block_stream(stream);

		let hash = BlakeTwo256::hash(b"42");
		let r: Result<(), ()> = sender.notify(|| Ok(hash));
		r.unwrap();

		// Verify RPC `beefy_getFinalizedHead` returns expected hash.
		let request = r#"{"jsonrpc":"2.0","method":"beefy_getFinalizedHead","params":[],"id":1}"#;
		let expected = "{\
			\"jsonrpc\":\"2.0\",\
			\"result\":\"0x2f0039e93a27221fcf657fb877a1d4f60307106113e885096cb44a461cd0afbf\",\
			\"id\":1\
		}"
		.to_string();
		let not_ready = "{\
			\"jsonrpc\":\"2.0\",\
			\"error\":{\"code\":1,\"message\":\"BEEFY RPC endpoint not ready\"},\
			\"id\":1\
		}"
		.to_string();

		let deadline = std::time::Instant::now() + std::time::Duration::from_secs(2);
		while std::time::Instant::now() < deadline {
			let (response, _) = io.raw_json_request(request).await.expect("RPC requests work");
			if response != not_ready {
				assert_eq!(response, expected);
				// Success
				return
			}
			std::thread::sleep(std::time::Duration::from_millis(50))
		}

		panic!(
			"Deadline reached while waiting for best BEEFY block to update. Perhaps the background task is broken?"
		);
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

		assert_eq!(response, r#"{"jsonrpc":"2.0","result":true,"id":1}"#);

		// Unsubscribe again and fail
		let (response, _) = rpc.raw_json_request(&unsub_req).await.unwrap();
		let expected = r#"{"jsonrpc":"2.0","result":false,"id":1}"#;

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
		let expected = r#"{"jsonrpc":"2.0","result":false,"id":1}"#;

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
