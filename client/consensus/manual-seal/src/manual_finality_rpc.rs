// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! RPC interface for the `ManualSeal` Engine.

use sp_consensus::ImportedAux;
use jsonrpc_core::Error;
use jsonrpc_derive::rpc;
use futures::{
	channel::{mpsc, oneshot},
	TryFutureExt,
	FutureExt,
	SinkExt
};
use serde::{Deserialize, Serialize};
use sp_runtime::Justification;
pub use self::gen_client::Client as ManualSealClient;

/// Future's type for jsonrpc
type FutureResult<T> = Box<dyn jsonrpc_core::futures::Future<Item = T, Error = Error> + Send>;
/// sender passed to the authorship task to report errors or successes.
pub type Sender<T> = Option<oneshot::Sender<std::result::Result<T, crate::Error>>>;

/// Message that instructs the background finality task, to finalize a block.
/// Usually sent over RPC
pub struct FinalizeBlockCommand<Hash> {
	/// Hash of the block to finalize
	pub hash: Hash,
	/// Channel to report errors/success to the rpc.
	pub sender: Sender<()>,
	/// Finalization justification
	pub justification: Option<Justification>,
}

/// RPC trait that provides method for interacting with the manual-finality task over rpc.
#[rpc]
pub trait ManualFinalityApi<Hash> {
	/// Instructs the manual finality task to finalize a block
	#[rpc(name = "engine_finalizeBlock")]
	fn finalize_block(
		&self,
		hash: Hash,
		justification: Option<Justification>
	) -> FutureResult<bool>;
}

/// A struct that implements the `ManualFinalityApi`.
pub struct ManualFinality<Hash> {
	finalize_block_channel: mpsc::Sender<FinalizeBlockCommand<Hash>>,
}

impl<Hash> ManualFinality<Hash> {
	/// Create new `ManualSeal` with the given reference to the client.
	pub fn new(finalize_block_channel: mpsc::Sender<FinalizeBlockCommand<Hash>>) -> Self {
		Self { finalize_block_channel }
	}
}

impl<Hash: Send + 'static> ManualFinalityApi<Hash> for ManualFinality<Hash> {
	fn finalize_block(&self, hash: Hash, justification: Option<Justification>) -> FutureResult<bool> {
		let mut sink = self.finalize_block_channel.clone();
		let future = async move {
			let (sender, receiver) = oneshot::channel();
			sink.send(
				FinalizeBlockCommand { hash, sender: Some(sender), justification }
			).await?;

			receiver.await?.map(|_| true)
		};

		Box::new(future.boxed().map_err(Error::from).compat())
	}
}

/// report any errors or successes encountered by the authorship task back
/// to the rpc
pub fn send_result<T: std::fmt::Debug>(
	sender: &mut Sender<T>,
	result: std::result::Result<T, crate::Error>
) {
	if let Some(sender) = sender.take() {
		if let Err(err) = sender.send(result) {
			log::warn!("Server is shutting down: {:?}", err)
		}
	} else {
		// instant seal doesn't report errors over rpc, simply log them.
		match result {
			Ok(r) => log::info!("Instant Seal success: {:?}", r),
			Err(e) => log::error!("Instant Seal encountered an error: {}", e)
		}
	}
}
