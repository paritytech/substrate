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

//! RPC interface for the ManualSeal Engine.
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

/// Message sent to the background authorship task. Tells the engine to propose a new block.
pub struct CreateBlockCommand<Hash> {
		/// If set, author an empty block when there are no transactions in the ppol.
		/// If not set, Error::EmptyTransactionPool is returned.
		pub create_empty: bool,
		/// Whether to instantly finalize the created block.
		pub finalize: bool,
		/// The parent hash of the about-to-be-created block. If `None` use the best block.
		pub parent_hash: Option<Hash>,
		/// Sender to report errors/success to the caller.
		pub sender: Sender<CreatedBlock<Hash>>,
}

/// RPC trait that provides methods for interacting with the manual-seal authorship task over rpc.
#[rpc]
pub trait ManualSealApi<Hash> {
	/// Instructs the manual-seal authorship task to create a new block
	#[rpc(name = "engine_createBlock")]
	fn create_block(
		&self,
		create_empty: bool,
		finalize: bool,
		parent_hash: Option<Hash>
	) -> FutureResult<CreatedBlock<Hash>>;
}

/// A struct that implements the [`ManualSealApi`].
pub struct ManualSeal<Hash> {
	import_block_channel: mpsc::Sender<CreateBlockCommand<Hash>>,
}

/// return type of `engine_createBlock`
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
		create_empty: bool,
		finalize: bool,
		parent_hash: Option<Hash>
	) -> FutureResult<CreatedBlock<Hash>> {
		let mut sink = self.import_block_channel.clone();
		let future = async move {
			let (sender, receiver) = oneshot::channel();
			let command = CreateBlockCommand {
				create_empty,
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
