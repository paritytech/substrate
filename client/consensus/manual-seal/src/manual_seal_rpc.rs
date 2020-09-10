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
pub use self::gen_client::Client as ManualSealClient;

/// Future's type for jsonrpc
type FutureResult<T> = Box<dyn jsonrpc_core::futures::Future<Item = T, Error = Error> + Send>;
/// sender passed to the authorship task to report errors or successes.
pub type Sender<T> = Option<oneshot::Sender<std::result::Result<T, crate::Error>>>;

/// Message that instructs the background authorship task, to author a new block.
/// Usually sent over RPC
pub struct CreateBlockCommand<Hash> {
	/// Whether empty blocks (without extrinsics) should be created.
	/// When false, may return Error::EmptyTransactionPool.
	pub allow_empty: bool,
	/// Instantly finalize this block?
	pub finalize: bool,
	/// The parent hash of the about-to-created block
	pub parent_hash: Option<Hash>,
	/// Channel to report errors/success to the rpc.
	pub sender: Sender<CreatedBlock<Hash>>,
}

/// RPC trait that provides method for interacting with the manual-seal authorship task over rpc.
#[rpc]
pub trait ManualSealApi<Hash> {
	/// Instructs the manual-seal authorship task to create a new block
	#[rpc(name = "engine_createBlock")]
	fn create_block(
		&self,
		allow_empty: bool,
		finalize: bool,
		parent_hash: Option<Hash>
	) -> FutureResult<CreatedBlock<Hash>>;
}

/// A struct that implements the [`ManualSealApi`].
pub struct ManualSeal<Hash> {
	import_block_channel: mpsc::Sender<CreateBlockCommand<Hash>>,
}

/// Response message sent by the authorship task.
#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
pub struct CreatedBlock<Hash> {
	/// hash of the created block.
	pub hash: Hash,
	/// some extra details about the import operation
	pub aux: ImportedAux
}

impl<Hash> ManualSeal<Hash> {
	/// Create new `ManualSeal` with the given reference to the client.
	pub fn new(import_block_channel: mpsc::Sender<CreateBlockCommand<Hash>>) -> Self {
		Self { import_block_channel }
	}
}

impl<Hash: Send + 'static> ManualSealApi<Hash> for ManualSeal<Hash> {
	fn create_block(
		&self,
		allow_empty: bool,
		finalize: bool,
		parent_hash: Option<Hash>
	) -> FutureResult<CreatedBlock<Hash>> {
		let mut sink = self.import_block_channel.clone();
		let future = async move {
			let (sender, receiver) = oneshot::channel();
			let command = CreateBlockCommand {
				allow_empty,
				finalize,
				parent_hash,
				sender: Some(sender),
			};
			sink.send(command).await?;
			receiver.await?
		}.boxed();

		Box::new(future.map_err(Error::from).compat())
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
