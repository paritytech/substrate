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

use std::{self, io::{Read, Write}};
use futures::prelude::*;
use log::{info, warn};

use runtime_primitives::generic::{SignedBlock, BlockId};
use runtime_primitives::traits::{SaturatedConversion, Zero, One, Block, Header, NumberFor};
use consensus_common::import_queue::{ImportQueue, IncomingBlock, Link};
use network::message;

use consensus_common::BlockOrigin;
use crate::components::{self, Components, ServiceFactory, FactoryFullConfiguration, FactoryBlockNumber, RuntimeGenesis};
use crate::new_client;
use parity_codec::{Decode, Encode};
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
}

impl WaitLink {
	fn new() -> WaitLink {
		WaitLink {
			imported_blocks: 0,
		}
	}
}

impl<B: Block> Link<B> for WaitLink {
	fn block_imported(&mut self, _hash: &B::Hash, _number: NumberFor<B>) {
		self.imported_blocks += 1;
	}
}

/// Import blocks from a binary stream.
pub fn import_blocks<F, E, R>(
	mut config: FactoryFullConfiguration<F>,
	exit: E,
	mut input: R
) -> error::Result<()>
	where F: ServiceFactory, E: Future<Item=(),Error=()> + Send + 'static, R: Read,
{
	let client = new_client::<F>(&config)?;
	// FIXME #1134 this shouldn't need a mutable config.
	let select_chain = components::FullComponents::<F>::build_select_chain(&mut config, client.clone())?;
	let mut queue = components::FullComponents::<F>::build_import_queue(&mut config, client.clone(), select_chain)?;

	let (exit_send, exit_recv) = std::sync::mpsc::channel();
	::std::thread::spawn(move || {
		let _ = exit.wait();
		let _ = exit_send.send(());
	});

	let count: u64 = Decode::decode(&mut input).ok_or("Error reading file")?;
	info!("Importing {} blocks", count);
	let mut block_count = 0;
	for b in 0 .. count {
		if exit_recv.try_recv().is_ok() {
			break;
		}
		if let Some(signed) = SignedBlock::<F::Block>::decode(&mut input) {
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
				IncomingBlock::<F::Block>{
					hash: block.hash,
					header: block.header,
					body: block.body,
					justification: block.justification,
					origin: None,
				}
			]);
		} else {
			warn!("Error reading block data at {}.", b);
			break;
		}

		block_count = b;
		if b % 1000 == 0 {
			info!("#{} blocks were added to the queue", b);
		}
	}

	let mut link = WaitLink::new();
	tokio::run(futures::future::poll_fn(move || {
		let blocks_before = link.imported_blocks;
		queue.poll_actions(&mut link);
		if link.imported_blocks / 1000 != blocks_before / 1000 {
			info!(
				"#{} blocks were imported (#{} left)",
				link.imported_blocks,
				count - link.imported_blocks
			);
		}
		if link.imported_blocks >= count {
			Ok(Async::Ready(()))
		} else {
			Ok(Async::NotReady)
		}
	}));

	info!("Imported {} blocks. Best: #{}", block_count, client.info().chain.best_number);

	Ok(())
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
