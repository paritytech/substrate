// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Substrate RPC implementation.
//!
//! A core implementation of Substrate RPC interfaces.

#![warn(missing_docs)]

pub use jsonrpsee::core::{
	id_providers::{
		RandomIntegerIdProvider as RandomIntegerSubscriptionId,
		RandomStringIdProvider as RandomStringSubscriptionId,
	},
	traits::IdProvider as RpcSubscriptionIdProvider,
};
pub use sc_rpc_api::DenyUnsafe;

pub mod author;
pub mod chain;
pub mod dev;
pub mod offchain;
pub mod state;
pub mod statement;
pub mod system;

#[cfg(any(test, feature = "test-helpers"))]
pub mod testing;

/// Task executor that is being used by RPC subscriptions.
pub type SubscriptionTaskExecutor = std::sync::Arc<dyn sp_core::traits::SpawnNamed>;

/// JSON-RPC helpers.
pub mod utils {
	use futures::{Future, FutureExt, Stream, StreamExt};
	use jsonrpsee::{
		PendingSubscriptionSink, SendTimeoutError, SubscriptionMessage, SubscriptionSink,
	};
	use sp_runtime::Serialize;

	use crate::SubscriptionTaskExecutor;

	/// Similar to [`pipe_from_stream`] but also attempts to accept the subscription.
	#[inline(never)]
	pub async fn accept_and_pipe_from_stream<S, T>(pending: PendingSubscriptionSink, stream: S)
	where
		S: Stream<Item = T> + Unpin + Send + 'static,
		T: Serialize + Send + 'static,
	{
		let Ok(sink) = pending.accept().await else { return };
		pipe_from_stream(sink, stream).await
	}

	/// Feed items to the subscription from the underlying stream.
	/// If the subscription can't keep up with the underlying stream
	/// then it's dropped.
	///
	/// This is simply a way to keep previous behaviour with unbounded streams
	/// and should be replaced by specific RPC endpoint behaviour.
	#[inline(never)]
	pub async fn pipe_from_stream<S, T>(sink: SubscriptionSink, mut stream: S)
	where
		S: Stream<Item = T> + Unpin + Send + 'static,
		T: Serialize + Send + 'static,
	{
		loop {
			tokio::select! {
				biased;
				_ = sink.closed() => break,

				maybe_item = stream.next() => {
					let msg = match maybe_item {
						// Some(item) => SubscriptionMessage::new(sink.method_name(), sink.subscription_id(), &item).expect("JSON serialization infallible; qed"),
						Some(item) => {
							// let x = serde_json::to_string(&item).unwrap();
							// bytes_serialized += x.len();
							// num_msgs += 1;
							SubscriptionMessage::new(sink.method_name(), sink.subscription_id(), &item).expect("JSON serialization infallible; qed")
						}
						None => break,
					};

					match sink.send_timeout(msg, std::time::Duration::from_secs(60)).await {
						Ok(_) => (),
						Err(SendTimeoutError::Closed(_)) => break,
						Err(SendTimeoutError::Timeout(_)) => {
							log::warn!(target: "rpc", "dropping subscription; timeout");
							break
						}
					}
				}
			}
		}
	}

	/// Build a subscription message.
	///
	/// # Panics
	///
	/// This function panics if the `Serialize` fails and is treated a bug.
	pub fn to_sub_message(result: &impl Serialize) -> SubscriptionMessage {
		SubscriptionMessage::from_json(result).expect("JSON serialization infallible; qed")
	}

	pub fn to_sub_message_v2(
		sink: &SubscriptionSink,
		result: &impl Serialize,
	) -> SubscriptionMessage {
		SubscriptionMessage::new(sink.method_name(), sink.subscription_id(), result)
			.expect("Serialize infallible; qed")
	}

	/// Spawn a subscription task and wait until it completes.
	pub fn spawn_subscription_task(
		executor: &SubscriptionTaskExecutor,
		fut: impl Future<Output = ()> + Send + 'static,
	) {
		executor.spawn("substrate-rpc-subscription", Some("rpc"), fut.boxed());
	}
}
