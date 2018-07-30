// Copyright 2017 Parity Technologies (UK) Ltd.
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
use futures::Future;
use serde_json;

use client::BlockOrigin;
use runtime_primitives::generic::{SignedBlock, BlockId};
use runtime_primitives::traits::{As};
use components::{ServiceFactory, FactoryFullConfiguration, FactoryBlockNumber, RuntimeGenesis};
use new_client;
use codec::{Decode, Encode};
use error;
use chain_spec::ChainSpec;

/// Export a range of blocks to a binary stream.
pub fn export_blocks<F, E, W>(config: FactoryFullConfiguration<F>, exit: E, mut output: W, from: FactoryBlockNumber<F>, to: Option<FactoryBlockNumber<F>>, json: bool) -> error::Result<()>
	where F: ServiceFactory, E: Future<Item=(),Error=()> + Send + 'static, W: Write,
{
	let client = new_client::<F>(config)?;
	let mut block = from;

	let last = match to {
		Some(v) if v == As::sa(0) => As::sa(1),
		Some(v) => v,
		None => client.info()?.chain.best_number,
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
		output.write(&(last - block + As::sa(1)).encode())?;
	}

	loop {
		if exit_recv.try_recv().is_ok() {
			break;
		}
		match client.block(&BlockId::number(block))? {
			Some(block) => {
				if json {
					serde_json::to_writer(&mut output, &block).map_err(|e| format!("Eror writing JSON: {}", e))?;
				} else {
					output.write(&block.encode())?;
				}
			},
			None => break,
		}
		if block.as_() % 10000 == 0 {
			info!("#{}", block);
		}
		if block == last {
			break;
		}
		block += As::sa(1);
	}
	Ok(())
}

/// Import blocks from a binary stream.
pub fn import_blocks<F, E, R>(config: FactoryFullConfiguration<F>, exit: E, mut input: R) -> error::Result<()>
	where F: ServiceFactory, E: Future<Item=(),Error=()> + Send + 'static, R: Read,
{
	let client = new_client::<F>(config)?;

	let (exit_send, exit_recv) = std::sync::mpsc::channel();
	::std::thread::spawn(move || {
		let _ = exit.wait();
		let _ = exit_send.send(());
	});

	let count: u32 = Decode::decode(&mut input).ok_or("Error reading file")?;
	info!("Importing {} blocks", count);
	let mut block = 0;
	for _ in 0 .. count {
		if exit_recv.try_recv().is_ok() {
			break;
		}
		match SignedBlock::decode(&mut input) {
			Some(block) => {
				let header = client.check_justification(block.block.header, block.justification.into())?;
				client.import_block(BlockOrigin::File, header, Some(block.block.extrinsics))?;
			},
			None => {
				warn!("Error reading block data.");
				break;
			}
		}
		block += 1;
		if block % 1000 == 0 {
			info!("#{}", block);
		}
	}
	info!("Imported {} blocks. Best: #{}", block, client.info()?.chain.best_number);

	Ok(())
}

/// Revert the chain.
pub fn revert_chain<F>(config: FactoryFullConfiguration<F>, blocks: FactoryBlockNumber<F>) -> error::Result<()>
	where F: ServiceFactory,
{
	let client = new_client::<F>(config)?;
	let reverted = client.revert(blocks)?;
	let info = client.info()?.chain;
	info!("Reverted {} blocks. Best: #{} ({})", reverted, info.best_number, info.best_hash);
	Ok(())
}

/// Build a chain spec json
pub fn build_spec<G>(spec: ChainSpec<G>, raw: bool) -> error::Result<String>
	where G: RuntimeGenesis,
{
	Ok(spec.to_json(raw)?)
}
