// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! RPC interface for the `ManualSeal` Engine.

use crate::error::Error;
use futures::{
	channel::{mpsc, oneshot},
	FutureExt, SinkExt,
};
use jsonrpsee::types::{Error as JsonRpseeError, RpcModule};
use sc_consensus::ImportedAux;
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use sp_runtime::EncodedJustification;

/// Helper macro to bail early in async context when you want to
/// return `Box::pin(future::err(e))` once an error occurs.
/// Because `Try` is not implemented for it.
macro_rules! unwrap_or_fut_err {
	( $e:expr ) => {
		match $e {
			Ok(x) => x,
			Err(e) => return Box::pin(futures::future::err(e.into())),
		}
	};
}

/// Sender passed to the authorship task to report errors or successes.
pub type Sender<T> = Option<oneshot::Sender<std::result::Result<T, Error>>>;

/// Message sent to the background authorship task, usually by RPC.
pub enum EngineCommand<Hash> {
	/// Tells the engine to propose a new block
	///
	/// if create_empty == true, it will create empty blocks if there are no transactions
	/// in the transaction pool.
	///
	/// if finalize == true, the block will be instantly finalized.
	SealNewBlock {
		/// if true, empty blocks(without extrinsics) will be created.
		/// otherwise, will return Error::EmptyTransactionPool.
		create_empty: bool,
		/// instantly finalize this block?
		finalize: bool,
		/// specify the parent hash of the about-to-created block
		parent_hash: Option<Hash>,
		/// sender to report errors/success to the rpc.
		sender: Sender<CreatedBlock<Hash>>,
	},
	/// Tells the engine to finalize the block with the supplied hash
	FinalizeBlock {
		/// hash of the block
		hash: Hash,
		/// sender to report errors/success to the rpc.
		sender: Sender<()>,
		/// finalization justification
		justification: Option<EncodedJustification>,
	},
}

/// A struct that implements the [`ManualSealApi`].
pub struct ManualSeal<Hash> {
	import_block_channel: mpsc::Sender<EngineCommand<Hash>>,
}

/// return type of `engine_createBlock`
#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
pub struct CreatedBlock<Hash> {
	/// hash of the created block.
	pub hash: Hash,
	/// some extra details about the import operation
	pub aux: ImportedAux,
}

impl<Hash> ManualSeal<Hash> {
	/// Create new `ManualSeal` with the given reference to the client.
	pub fn new(import_block_channel: mpsc::Sender<EngineCommand<Hash>>) -> Self {
		Self { import_block_channel }
	}
}

// TODO(niklasad1): this should be replaced with a proc macro impl.
impl<Hash: Send + Sync + DeserializeOwned + Serialize + 'static> ManualSeal<Hash> {
	/// Convert a [`ManualSealApi`] to an [`RpcModule`]. Registers all the RPC methods available
	/// with the RPC server.
	pub fn into_rpc_module(self) -> std::result::Result<RpcModule<Self>, JsonRpseeError> {
		let mut module = RpcModule::new(self);

		module.register_async_method::<CreatedBlock<Hash>, _>(
			"engine_createBlock",
			|params, engine| {
				let mut seq = params.sequence();

				let create_empty = unwrap_or_fut_err!(seq.next());
				let finalize = unwrap_or_fut_err!(seq.next());
				let parent_hash = unwrap_or_fut_err!(seq.optional_next());
				let mut sink = engine.import_block_channel.clone();

				async move {
					let (sender, receiver) = oneshot::channel();
					// NOTE: this sends a Result over the channel.
					let command = EngineCommand::SealNewBlock {
						create_empty,
						finalize,
						parent_hash,
						sender: Some(sender),
					};

					sink.send(command).await?;

					match receiver.await {
						Ok(Ok(rx)) => Ok(rx),
						Ok(Err(e)) => Err(e.into()),
						Err(e) => Err(JsonRpseeError::to_call_error(e)),
					}
				}
				.boxed()
			},
		)?;

		module.register_async_method("engine_finalizeBlock", |params, engine| {
			let mut seq = params.sequence();

			let hash = unwrap_or_fut_err!(seq.next());
			let justification = unwrap_or_fut_err!(seq.optional_next());
			let mut sink = engine.import_block_channel.clone();

			async move {
				let (sender, receiver) = oneshot::channel();
				let command =
					EngineCommand::FinalizeBlock { hash, sender: Some(sender), justification };
				sink.send(command).await?;
				receiver.await.map(|_| true).map_err(|e| JsonRpseeError::to_call_error(e))
			}
			.boxed()
		})?;

		Ok(module)
	}
}

/// report any errors or successes encountered by the authorship task back
/// to the rpc
pub fn send_result<T: std::fmt::Debug>(
	sender: &mut Sender<T>,
	result: std::result::Result<T, crate::Error>,
) {
	if let Some(sender) = sender.take() {
		if let Err(err) = sender.send(result) {
			log::warn!("Server is shutting down: {:?}", err)
		}
	} else {
		// instant seal doesn't report errors over rpc, simply log them.
		match result {
			Ok(r) => log::info!("Instant Seal success: {:?}", r),
			Err(e) => log::error!("Instant Seal encountered an error: {}", e),
		}
	}
}
