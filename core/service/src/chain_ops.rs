// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

use std::{self, io::{Read, Write, Seek}};
use futures::prelude::*;
use futures03::TryFutureExt as _;
use log::{info, warn};

use sr_primitives::generic::{SignedBlock, BlockId};
use sr_primitives::traits::{SaturatedConversion, Zero, One, Block, Header, NumberFor};
use consensus_common::import_queue::{ImportQueue, IncomingBlock, Link, BlockImportError, BlockImportResult};
use network::message;

use consensus_common::BlockOrigin;
use crate::components::{self, Components, ServiceFactory, FactoryFullConfiguration, FactoryBlockNumber, RuntimeGenesis};
use crate::new_client;
use codec::{Decode, Encode, IoReader};
use crate::error;
use crate::chain_spec::ChainSpec;

/// Export a range of blocks to a binary stream.
pub fn export_blocks<F, E, W>(
	config: FactoryFullConfiguration<F>,
	exit: E,
	mut output: W,
	from: FactoryBlockNumber<F>,
	to: Option<FactoryBlockNumber<F>>,
	json: bool
) -> error::Result<()>
	where
	F: ServiceFactory,
	E: Future<Item=(),Error=()> + Send + 'static,
	W: Write,
{
	let client = new_client::<F>(&config)?;
	let mut block = from;

	let last = match to {
		Some(v) if v.is_zero() => One::one(),
		Some(v) => v,
		None => client.info().chain.best_number,
	};

	if last < block {
		return Err("Invalid block range specified".into());
	}

	let (exit_send, exit_recv) = std::sync::mpsc::channel();
	::std::thread::spawn(move || {
		let _ = exit.wait();
		let _ = exit_send.send(());
	});
	info!("Exporting blocks from #{} to #{}", block, last);
	if !json {
		let last_: u64 = last.saturated_into::<u64>();
		let block_: u64 = block.saturated_into::<u64>();
		let len: u64 = last_ - block_ + 1;
		output.write(&len.encode())?;
	}

	loop {
		if exit_recv.try_recv().is_ok() {
			break;
		}
		match client.block(&BlockId::number(block))? {
			Some(block) => {
				if json {
					serde_json::to_writer(&mut output, &block)
						.map_err(|e| format!("Error writing JSON: {}", e))?;
				} else {
					output.write(&block.encode())?;
				}
			},
			None => break,
		}
		if (block % 10000.into()).is_zero() {
			info!("#{}", block);
		}
		if block == last {
			break;
		}
		block += One::one();
	}
	Ok(())
}

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

impl<B: Block> Link<B> for WaitLink {
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

/// Returns a future that import blocks from a binary stream.
pub fn import_blocks<F, E, R>(
	mut config: FactoryFullConfiguration<F>,
	exit: E,
	input: R
) -> error::Result<impl Future<Item = (), Error = ()>>
	where F: ServiceFactory, E: Future<Item=(),Error=()> + Send + 'static, R: Read + Seek,
{
	let client = new_client::<F>(&config)?;
	// FIXME #1134 this shouldn't need a mutable config.
	let select_chain = components::FullComponents::<F>::build_select_chain(&mut config, client.clone())?;
	let (mut queue, _) = components::FullComponents::<F>::build_import_queue(
		&mut config,
		client.clone(),
		select_chain,
		None,
		None,
	)?;

	let (exit_send, exit_recv) = std::sync::mpsc::channel();
	::std::thread::spawn(move || {
		let _ = exit.wait();
		let _ = exit_send.send(());
	});

	let mut io_reader_input = IoReader(input);
	let count: u64 = Decode::decode(&mut io_reader_input)
		.map_err(|e| format!("Error reading file: {}", e))?;
	info!("Importing {} blocks", count);
	let mut block_count = 0;
	for b in 0 .. count {
		if exit_recv.try_recv().is_ok() {
			break;
		}
		match SignedBlock::<F::Block>::decode(&mut io_reader_input) {
			Ok(signed) => {
				let (header, extrinsics) = signed.block.deconstruct();
				let hash = header.hash();
				let block  = message::BlockData::<F::Block> {
					hash,
					justification: signed.justification,
					header: Some(header),
					body: Some(extrinsics),
					receipt: None,
					message_queue: None
				};
				// import queue handles verification and importing it into the client
				queue.import_blocks(BlockOrigin::File, vec![
					IncomingBlock::<F::Block> {
						hash: block.hash,
						header: block.header,
						body: block.body,
						justification: block.justification,
						origin: None,
					}
				]);
			}
			Err(e) => {
				warn!("Error reading block data at {}: {}", b, e);
				break;
			}
		}

		block_count = b;
		if b % 1000 == 0 && b != 0 {
			info!("#{} blocks were added to the queue", b);
		}
	}

	let mut link = WaitLink::new();
	Ok(futures::future::poll_fn(move || {
		if exit_recv.try_recv().is_ok() {
			return Ok(Async::Ready(()));
		}

		let blocks_before = link.imported_blocks;
		let _ = futures03::future::poll_fn(|cx| {
			queue.poll_actions(cx, &mut link);
			std::task::Poll::Pending::<Result<(), ()>>
		}).compat().poll();
		if link.has_error {
			info!(
				"Stopping after #{} blocks because of an error",
				link.imported_blocks,
			);
			return Ok(Async::Ready(()));
		}
		if link.imported_blocks / 1000 != blocks_before / 1000 {
			info!(
				"#{} blocks were imported (#{} left)",
				link.imported_blocks,
				count - link.imported_blocks
			);
		}
		if link.imported_blocks >= count {
			info!("Imported {} blocks. Best: #{}", block_count, client.info().chain.best_number);
			Ok(Async::Ready(()))
		} else {
			Ok(Async::NotReady)
		}
	}))
}

/// Revert the chain.
pub fn revert_chain<F>(
	config: FactoryFullConfiguration<F>,
	blocks: FactoryBlockNumber<F>
) -> error::Result<()>
	where F: ServiceFactory,
{
	let client = new_client::<F>(&config)?;
	let reverted = client.revert(blocks)?;
	let info = client.info().chain;

	if reverted.is_zero() {
		info!("There aren't any non-finalized blocks to revert.");
	} else {
		info!("Reverted {} blocks. Best: #{} ({})", reverted, info.best_number, info.best_hash);
	}
	Ok(())
}

/// Build a chain spec json
pub fn build_spec<G>(spec: ChainSpec<G>, raw: bool) -> error::Result<String>
	where G: RuntimeGenesis,
{
	Ok(spec.to_json(raw)?)
}
