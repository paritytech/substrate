// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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
use futures::{future, FutureExt, StreamExt};
use jsonrpsee::{
	proc_macros::rpc,
	types::{Error as JsonRpseeError, RpcResult},
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
		name = "subscribeJustifications"
		aliases = "beefy_justifications",
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
		Self {
			signed_commitment_stream,
			executor,
		}
	}
}

impl<Block> BeefyApiServer<notification::SignedCommitment, Block> for BeefyRpcHandler<Block>
where
	Block: BlockT,
{
	fn subscribe_justifications(&self, mut sink: SubscriptionSink) -> RpcResult<()> {
		fn log_err(err: JsonRpseeError) -> bool {
			log::error!(
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

		self.executor.execute(fut);
		Ok(())
	}
}
