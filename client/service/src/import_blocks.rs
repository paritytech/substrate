// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Chain utilities.

#![allow(unused_imports)]

use crate::error;
//use crate::builder::{ServiceBuilderCommand, ServiceBuilder};
use crate::error::Error;
use sc_chain_spec::ChainSpec;
use log::{warn, info};
use futures::{future, prelude::*};
use sp_runtime::traits::{
	Block as BlockT, NumberFor, One, Zero, Header, SaturatedConversion
};
use sp_runtime::generic::{BlockId, SignedBlock};
use codec::{Decode, Encode, IoReader};
use sc_client::{Client, LocalCallExecutor};
use sp_consensus::{
	BlockOrigin,
	import_queue::{IncomingBlock, Link, BlockImportError, BlockImportResult, ImportQueue},
};
use sc_executor::{NativeExecutor, NativeExecutionDispatch};

use std::{io::{Read, Write, Seek}, pin::Pin};
use sc_client_api::BlockBackend;
use std::sync::Arc;

pub fn import_blocks<B, BA, CE, IQ>(
	client: Arc<Client<BA, CE, B, ()>>,
	import_queue: &'static mut IQ,
	input: impl Read + Seek + Send + 'static,
	force: bool,
) -> Pin<Box<dyn Future<Output = Result<(), Error>> + Send>>
where
	B: BlockT,
	BA: sc_client_api::backend::Backend<B> + 'static,
	CE: sc_client_api::call_executor::CallExecutor<B> + Send + Sync + 'static,
	IQ: ImportQueue<B> + Sync + 'static,
{
	struct WaitLink {
		imported_blocks: u64,
		has_error: bool,
	}

	impl WaitLink {
		fn new() -> WaitLink {
			WaitLink {
				imported_blocks: 0,
				has_error: false,
			}
		}
	}

	impl<B: BlockT> Link<B> for WaitLink {
		fn blocks_processed(
			&mut self,
			imported: usize,
			_count: usize,
			results: Vec<(Result<BlockImportResult<NumberFor<B>>, BlockImportError>, B::Hash)>
		) {
			self.imported_blocks += imported as u64;

			for result in results {
				if let (Err(err), hash) = result {
					warn!("There was an error importing block with hash {:?}: {:?}", hash, err);
					self.has_error = true;
					break;
				}
			}
		}
	}

	let client = client;
	let mut queue = import_queue;

	let mut io_reader_input = IoReader(input);
	let mut count = None::<u64>;
	let mut read_block_count = 0;
	let mut link = WaitLink::new();

	// Importing blocks is implemented as a future, because we want the operation to be
	// interruptible.
	//
	// Every time we read a block from the input or import a bunch of blocks from the import
	// queue, the `Future` re-schedules itself and returns `Poll::Pending`.
	// This makes it possible either to interleave other operations in-between the block imports,
	// or to stop the operation completely.
	let import = future::poll_fn(move |cx| {
		// Start by reading the number of blocks if not done so already.
		let count = match count {
			Some(c) => c,
			None => {
				let c: u64 = match Decode::decode(&mut io_reader_input) {
					Ok(c) => c,
					Err(err) => {
						let err = format!("Error reading file: {}", err);
						return std::task::Poll::Ready(Err(From::from(err)));
					},
				};
				info!("📦 Importing {} blocks", c);
				count = Some(c);
				c
			}
		};

		// Read blocks from the input.
		if read_block_count < count {
			match SignedBlock::<B>::decode(&mut io_reader_input) {
				Ok(signed) => {
					let (header, extrinsics) = signed.block.deconstruct();
					let hash = header.hash();
					// import queue handles verification and importing it into the client
					queue.import_blocks(BlockOrigin::File, vec![
						IncomingBlock::<B> {
							hash,
							header: Some(header),
							body: Some(extrinsics),
							justification: signed.justification,
							origin: None,
							allow_missing_state: false,
							import_existing: force,
						}
					]);
				}
				Err(e) => {
					warn!("Error reading block data at {}: {}", read_block_count, e);
					return std::task::Poll::Ready(Ok(()));
				}
			}

			read_block_count += 1;
			if read_block_count % 1000 == 0 {
				info!("#{} blocks were added to the queue", read_block_count);
			}

			cx.waker().wake_by_ref();
			return std::task::Poll::Pending;
		}

		let blocks_before = link.imported_blocks;
		queue.poll_actions(cx, &mut link);

		if link.has_error {
			info!(
				"Stopping after #{} blocks because of an error",
				link.imported_blocks,
			);
			return std::task::Poll::Ready(Ok(()));
		}

		if link.imported_blocks / 1000 != blocks_before / 1000 {
			info!(
				"#{} blocks were imported (#{} left)",
				link.imported_blocks,
				count - link.imported_blocks
			);
		}

		if link.imported_blocks >= count {
			info!("🎉 Imported {} blocks. Best: #{}", read_block_count, client.chain_info().best_number);
			return std::task::Poll::Ready(Ok(()));

		} else {
			// Polling the import queue will re-schedule the task when ready.
			return std::task::Poll::Pending;
		}
	});
	Box::pin(import)
}
