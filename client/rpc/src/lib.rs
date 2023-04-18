// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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
pub mod system;

#[cfg(any(test, feature = "test-helpers"))]
pub mod testing;

/// Task executor that is being used by RPC subscriptions.
pub type SubscriptionTaskExecutor = std::sync::Arc<dyn sp_core::traits::SpawnNamed>;

/// todo..
pub mod utils {
	use futures::{Stream, StreamExt};
	use jsonrpsee::{
		IntoSubscriptionCloseResponse, PendingSubscriptionSink, SendTimeoutError,
		SubscriptionCloseResponse, SubscriptionMessage, SubscriptionSink,
	};
	use sp_runtime::Serialize;

	/// RE-WRITE / REMOVE
	pub async fn accept_and_pipe_from_stream<S, T, R>(
		pending: PendingSubscriptionSink,
		stream: S,
	) -> SubscriptionResponse<R>
	where
		S: Stream<Item = T> + Unpin,
		T: Serialize,
		R: Serialize,
	{
		let Ok(sink )= pending.accept().await else {
			return SubscriptionResponse::Closed
		};
		pipe_from_stream(sink, stream).await
	}

	/// RE-WRITE / REMOVE
	pub async fn pipe_from_stream<S, T, R>(
		sink: SubscriptionSink,
		mut stream: S,
	) -> SubscriptionResponse<R>
	where
		S: Stream<Item = T> + Unpin,
		T: Serialize,
		R: Serialize,
	{
		loop {
			tokio::select! {
				biased;
				_ = sink.closed() => break SubscriptionResponse::Closed,

				maybe_item = stream.next() => {
					let item = match maybe_item {
						Some(item) => item,
						None => break SubscriptionResponse::Closed,
					};
					let msg = SubscriptionMessage::from_json(&item).expect("Serialize must be infallible; qed");

					match sink.send_timeout(msg, std::time::Duration::from_secs(60)).await {
						Ok(_) => (),
						Err(SendTimeoutError::Closed(_)) | Err(SendTimeoutError::Timeout(_)) => break SubscriptionResponse::Closed,
					}
				}
			}
		}
	}

	/// ...
	pub enum SubscriptionResponse<T> {
		/// The subscription was closed, no further message is sent.
		Closed,
		/// Send out a notification.
		Event(T),
	}

	impl<T: Serialize> IntoSubscriptionCloseResponse for SubscriptionResponse<T> {
		fn into_response(self) -> SubscriptionCloseResponse {
			match self {
				Self::Closed => SubscriptionCloseResponse::None,
				Self::Event(ev) => {
					let msg = SubscriptionMessage::from_json(&ev)
						.expect("JSON serialization infallible; qed");
					SubscriptionCloseResponse::Notif(msg)
				},
			}
		}
	}
}
