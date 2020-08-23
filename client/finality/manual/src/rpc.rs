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

//! RPC interface for the Manual Finality gadget.

use jsonrpc_core::Error;
use jsonrpc_derive::rpc;
use futures::{
	channel::{mpsc, oneshot},
	TryFutureExt,
	FutureExt,
	SinkExt
};
use sp_runtime::Justification;
pub use self::gen_client::Client as ManualSealClient;

/// Future's type for jsonrpc
type FutureResult<T> = Box<dyn jsonrpc_core::futures::Future<Item = T, Error = Error> + Send>;
/// sender passed to the authorship task to report errors or successes.
pub type Sender<T> = Option<oneshot::Sender<std::result::Result<T, crate::Error>>>;

/// Message sent to the background authorship task, usually by RPC.
pub struct FinalizeBlockCommand<Hash> {
	/// hash of the block
	pub hash: Hash,
	/// sender to report errors/success to the rpc.
	pub sender: Sender<()>,
	/// finalization justification
	pub justification: Option<Justification>,
}

/// RPC trait that provides methods for interacting with the manual-finality over rpc.
#[rpc]
pub trait ManualFinalityApi<Hash> {
	/// Instructs the manual-finality task to finalize a block
	#[rpc(name = "engine_finalizeBlock")]
	fn finalize_block(
		&self,
		hash: Hash,
		justification: Option<Justification>
	) -> FutureResult<bool>;
}

/// A struct that implements the `ManualFinalityApi`.
pub struct ManualFinality<Hash> {
	import_block_channel: mpsc::Sender<FinalizeBlockCommand<Hash>>,
}

impl<Hash> ManualFinality<Hash> {
	/// Create new `ManualFinality` with the given channel.
	pub fn new(import_block_channel: mpsc::Sender<FinalizeBlockCommand<Hash>>) -> Self {
		Self { import_block_channel }
	}
}

impl<Hash: Send + 'static> ManualFinalityApi<Hash> for ManualFinality<Hash> {

	fn finalize_block(&self, hash: Hash, justification: Option<Justification>) -> FutureResult<bool> {
		let mut sink = self.import_block_channel.clone();
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

/// report any errors or successes encountered by the finality gadget task back
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
		// instant finality doesn't report errors over rpc, simply log them.
		match result {
			Ok(r) => log::info!("Instant Finality success: {:?}", r),
			Err(e) => log::error!("Instant Finality encountered an error: {}", e)
		}
	}
}
