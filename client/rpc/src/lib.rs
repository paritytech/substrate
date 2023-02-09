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
		core::SubscriptionResult, PendingSubscriptionSink, SendTimeoutError, SubscriptionMessage,
		SubscriptionSink,
	};
	use sp_runtime::Serialize;
	use std::time::Duration;

	const SEND_TIMEOUT: Duration = Duration::from_secs(60);

	/// ...
	pub async fn accept_and_pipe_from_stream<S, T>(
		pending: PendingSubscriptionSink,
		stream: S,
	) -> SubscriptionResult
	where
		S: Stream<Item = T> + Unpin,
		T: Serialize,
	{
		let sink = pending.accept().await?;
		pipe_from_stream(sink, stream).await
	}

	/// ...
	pub async fn pipe_from_stream<S, T>(sink: SubscriptionSink, mut stream: S) -> SubscriptionResult
	where
		S: Stream<Item = T> + Unpin,
		T: Serialize,
	{
		let close_msg = loop {
			tokio::select! {
				biased;
				_ = sink.closed() => break None,

				maybe_item = stream.next() => {
					let item = match maybe_item {
						Some(item) => item,
						None => break None,
					};
					let msg = match SubscriptionMessage::from_json(&item) {
						Ok(msg) => msg,
						Err(e) => break Some(e.to_string()),
					};

					match sink.send_timeout(msg, SEND_TIMEOUT).await {
						Ok(_) => (),
						Err(SendTimeoutError::Closed(_)) => break None,
						Err(SendTimeoutError::Timeout(_)) => break Some("Subscription send timeout; subscription closed".to_string()),
					}
				}
			}
		};

		if let Some(msg) = close_msg {
			let msg = SubscriptionMessage::from_json(&msg)?;
			let _ = tokio::time::timeout(SEND_TIMEOUT, sink.close_with_error(msg)).await;
		}

		Ok(())
	}
}
