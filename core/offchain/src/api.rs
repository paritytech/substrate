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

use std::sync::Arc;
use futures::{Stream, Future, sync::mpsc};
use inherents::pool::InherentsPool;
use log::{info, debug, warn};
use parity_codec::Decode;
use primitives::OffchainExt;
use runtime_primitives::{
	generic::BlockId,
	traits::{self, Extrinsic},
};
use transaction_pool::txpool::{Pool, ChainApi};

/// A message between the offchain extension and the processing thread.
enum ExtMessage {
	SubmitExtrinsic(Vec<u8>),
}

/// Asynchronous offchain API.
///
/// NOTE this is done to prevent recursive calls into the runtime (which are not supported currently).
pub(crate) struct AsyncApi(mpsc::UnboundedSender<ExtMessage>);

impl OffchainExt for AsyncApi {
	fn submit_extrinsic(&mut self, ext: Vec<u8>) {
		let _ = self.0.unbounded_send(ExtMessage::SubmitExtrinsic(ext));
	}
}

/// Offchain extensions implementation API
pub(crate) struct Api<A: ChainApi> {
	receiver: Option<mpsc::UnboundedReceiver<ExtMessage>>,
	transaction_pool: Arc<Pool<A>>,
	inherents_pool: Arc<InherentsPool<<A::Block as traits::Block>::Extrinsic>>,
	at: BlockId<A::Block>,
}

impl<A: ChainApi> Api<A> {
	pub fn new(
		transaction_pool: Arc<Pool<A>>,
		inherents_pool: Arc<InherentsPool<<A::Block as traits::Block>::Extrinsic>>,
		at: BlockId<A::Block>,
	) -> (AsyncApi, Self) {
		let (tx, rx) = mpsc::unbounded();
		let api = Self {
			receiver: Some(rx),
			transaction_pool,
			inherents_pool,
			at,
		};
		(AsyncApi(tx), api)
	}

	/// Run a processing task for the API
	pub fn process(mut self) -> impl Future<Item=(), Error=()> {
		let receiver = self.receiver.take().expect("Take invoked only once.");

		receiver.for_each(move |msg| {
			match msg {
				ExtMessage::SubmitExtrinsic(ext) => self.submit_extrinsic(ext),
			}
			Ok(())
		})
	}

	fn submit_extrinsic(&mut self, ext: Vec<u8>) {
		let xt = match <A::Block as traits::Block>::Extrinsic::decode(&mut &*ext) {
			Some(xt) => xt,
			None => {
				warn!("Unable to decode extrinsic: {:?}", ext);
				return
			},
		};

		info!("Submitting to the pool: {:?} (isSigned: {:?})", xt, xt.is_signed());
		match self.transaction_pool.submit_one(&self.at, xt.clone()) {
			Ok(hash) => debug!("[{:?}] Offchain transaction added to the pool.", hash),
			Err(_) => {
				debug!("Offchain inherent added to the pool.");
				self.inherents_pool.add(xt);
			},
		}
	}
}
