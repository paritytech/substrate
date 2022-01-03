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

use beefy_gadget::notification::BeefySignedCommitmentStream;
use futures::{future, task::Spawn, FutureExt, StreamExt};
use jsonrpsee::{
	core::{Error as JsonRpseeError, RpcResult},
	proc_macros::rpc,
	SubscriptionSink,
};
use log::warn;
use sc_rpc::SubscriptionTaskExecutor;
use sp_runtime::traits::Block as BlockT;

mod notification;

/// Provides RPC methods for interacting with BEEFY.
#[rpc(client, server, namespace = "beefy")]
pub trait BeefyApi<Notification, Hash> {
	/// Returns the block most recently finalized by BEEFY, alongside side its justification.
	#[subscription(
		name = "subscribeJustifications" => "justifications",
		item = Notification,
	)]
	fn subscribe_justifications(&self) -> RpcResult<()>;
}

/// Implements the BeefyApi RPC trait for interacting with BEEFY.
pub struct BeefyRpcHandler<Block: BlockT> {
	signed_commitment_stream: BeefySignedCommitmentStream<Block>,
	executor: SubscriptionTaskExecutor,
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
		Self { signed_commitment_stream, executor }
	}
}

impl<Block> BeefyApiServer<notification::SignedCommitment, Block> for BeefyRpcHandler<Block>
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
			.map(|sc| notification::SignedCommitment::new::<Block>(sc));

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
}

#[cfg(test)]
mod tests {
	use super::*;

	use beefy_gadget::notification::{BeefySignedCommitmentSender, SignedCommitment};
	use beefy_primitives::{known_payload_ids, Payload};
	use codec::{Decode, Encode};
	use jsonrpsee::{types::EmptyParams, RpcModule};
	use substrate_test_runtime_client::runtime::Block;

	fn setup_io_handler() -> (RpcModule<BeefyRpcHandler<Block>>, BeefySignedCommitmentSender<Block>)
	{
		let (commitment_sender, commitment_stream) = BeefySignedCommitmentStream::channel();

		(
			BeefyRpcHandler::new(commitment_stream, sc_rpc::SubscriptionTaskExecutor::default())
				.into_rpc(),
			commitment_sender,
		)
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

	fn create_commitment() -> SignedCommitment<Block> {
		let payload = Payload::new(known_payload_ids::MMR_ROOT_ID, "Hello World!".encode());
		SignedCommitment::<Block> {
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
		commitment_sender.notify(commitment.clone());

		// Inspect what we received
		let (bytes, recv_sub_id) = sub.next::<sp_core::Bytes>().await.unwrap().unwrap();
		let recv_commitment: SignedCommitment<Block> = Decode::decode(&mut &bytes[..]).unwrap();
		assert_eq!(&recv_sub_id, sub.subscription_id());
		assert_eq!(recv_commitment, commitment);
	}
}
