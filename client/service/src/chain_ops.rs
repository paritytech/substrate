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

use crate::error;
use crate::builder::{ServiceBuilderCommand, ServiceBuilder};
use crate::error::Error;
use sc_chain_spec::{ChainSpec, RuntimeGenesis, Extension};
use log::{warn, info};
use futures::{future, prelude::*};
use sp_runtime::{BuildStorage, traits::{
		Block as BlockT, NumberFor, One, Zero, Header, SaturatedConversion
	}
};
use sp_runtime::generic::{BlockId, SignedBlock};
use codec::{Decode, Encode, IoReader};
use sc_client::{Client, ExecutionStrategy, StateMachine, LocalCallExecutor};
use sc_client_db::BenchmarkingState;
use sp_consensus::import_queue::{IncomingBlock, Link, BlockImportError, BlockImportResult, ImportQueue};
use sp_consensus::BlockOrigin;
use sc_executor::{NativeExecutor, NativeExecutionDispatch, WasmExecutionMethod};

use std::{io::{Read, Write, Seek}, pin::Pin};

use sc_network::message;

/// Build a chain spec json
pub fn build_spec<G, E>(spec: ChainSpec<G, E>, raw: bool) -> error::Result<String> where
	G: RuntimeGenesis,
	E: Extension,
{
	Ok(spec.to_json(raw)?)
}

/// Run runtime benchmarks.
pub fn benchmark_runtime<TBl, TExecDisp, G, E> (
	spec: ChainSpec<G, E>,
	strategy: ExecutionStrategy,
	wasm_method: WasmExecutionMethod,
) -> error::Result<()> where
	TBl: BlockT,
	TExecDisp: NativeExecutionDispatch + 'static,
	G: RuntimeGenesis,
	E: Extension,
{
	let genesis_storage = spec.build_storage()?;
	let mut changes = Default::default();
	let state = BenchmarkingState::<TBl>::new(genesis_storage)?;
	let executor = NativeExecutor::<TExecDisp>::new(
		wasm_method,
		None, // heap pages
	);
	let result = StateMachine::<_, _, NumberFor<TBl>, _>::new(
		&state,
		None,
		&mut changes,
		&executor,
		"IdentityBenchmarks_run_benchmarks",
		&[],
		Default::default(),
	).execute(strategy).map_err(|e| format!("Error executing runtime benchmark: {:?}", e))?;
	println!("{:?}", result);
	info!("Done.");
	Ok(())
}


impl<
	TBl, TRtApi, TGen, TCSExt, TBackend,
	TExecDisp, TFchr, TSc, TImpQu, TFprb, TFpp, TNetP,
	TExPool, TRpc, Backend
> ServiceBuilderCommand for ServiceBuilder<
	TBl, TRtApi, TGen, TCSExt,
	Client<TBackend, LocalCallExecutor<TBackend, NativeExecutor<TExecDisp>>, TBl, TRtApi>,
	TFchr, TSc, TImpQu, TFprb, TFpp, TNetP, TExPool, TRpc, Backend
> where
	TBl: BlockT,
	TBackend: 'static + sc_client_api::backend::Backend<TBl> + Send,
	TExecDisp: 'static + NativeExecutionDispatch,
	TImpQu: 'static + ImportQueue<TBl>,
	TRtApi: 'static + Send + Sync,
{
	type Block = TBl;
	type NativeDispatch = TExecDisp;

	fn import_blocks(
		self,
		input: impl Read + Seek + Send + 'static,
		force: bool,
	) -> Pin<Box<dyn Future<Output = Result<(), Error>> + Send>> {
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

		let client = self.client;
		let mut queue = self.import_queue;

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
					info!("Importing {} blocks", c);
					count = Some(c);
					c
				}
			};

			// Read blocks from the input.
			if read_block_count < count {
				match SignedBlock::<Self::Block>::decode(&mut io_reader_input) {
					Ok(signed) => {
						let (header, extrinsics) = signed.block.deconstruct();
						let hash = header.hash();
						let block  = message::BlockData::<Self::Block> {
							hash,
							justification: signed.justification,
							header: Some(header),
							body: Some(extrinsics),
							receipt: None,
							message_queue: None
						};
						// import queue handles verification and importing it into the client
						queue.import_blocks(BlockOrigin::File, vec![
							IncomingBlock::<Self::Block> {
								hash: block.hash,
								header: block.header,
								body: block.body,
								justification: block.justification,
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
				info!("Imported {} blocks. Best: #{}", read_block_count, client.chain_info().best_number);
				return std::task::Poll::Ready(Ok(()));

			} else {
				// Polling the import queue will re-schedule the task when ready.
				return std::task::Poll::Pending;
			}
		});
		Box::pin(import)
	}

	fn export_blocks(
		self,
		mut output: impl Write + 'static,
		from: NumberFor<TBl>,
		to: Option<NumberFor<TBl>>,
		json: bool
	) -> Pin<Box<dyn Future<Output = Result<(), Error>>>> {
		let client = self.client;
		let mut block = from;

		let last = match to {
			Some(v) if v.is_zero() => One::one(),
			Some(v) => v,
			None => client.chain_info().best_number,
		};

		let mut wrote_header = false;

		// Exporting blocks is implemented as a future, because we want the operation to be
		// interruptible.
		//
		// Every time we write a block to the output, the `Future` re-schedules itself and returns
		// `Poll::Pending`.
		// This makes it possible either to interleave other operations in-between the block exports,
		// or to stop the operation completely.
		let export = future::poll_fn(move |cx| {
			if last < block {
				return std::task::Poll::Ready(Err("Invalid block range specified".into()));
			}

			if !wrote_header {
				info!("Exporting blocks from #{} to #{}", block, last);
				if !json {
					let last_: u64 = last.saturated_into::<u64>();
					let block_: u64 = block.saturated_into::<u64>();
					let len: u64 = last_ - block_ + 1;
					output.write_all(&len.encode())?;
				}
				wrote_header = true;
			}

			match client.block(&BlockId::number(block))? {
				Some(block) => {
					if json {
						serde_json::to_writer(&mut output, &block)
							.map_err(|e| format!("Error writing JSON: {}", e))?;
						} else {
							output.write_all(&block.encode())?;
					}
				},
				// Reached end of the chain.
				None => return std::task::Poll::Ready(Ok(())),
			}
			if (block % 10000.into()).is_zero() {
				info!("#{}", block);
			}
			if block == last {
				return std::task::Poll::Ready(Ok(()));
			}
			block += One::one();

			// Re-schedule the task in order to continue the operation.
			cx.waker().wake_by_ref();
			std::task::Poll::Pending
		});

		Box::pin(export)
	}

	fn revert_chain(
		&self,
		blocks: NumberFor<TBl>
	) -> Result<(), Error> {
		let reverted = self.client.revert(blocks)?;
		let info = self.client.chain_info();

		if reverted.is_zero() {
			info!("There aren't any non-finalized blocks to revert.");
		} else {
			info!("Reverted {} blocks. Best: #{} ({})", reverted, info.best_number, info.best_hash);
		}
		Ok(())
	}

	fn check_block(
		self,
		block_id: BlockId<TBl>
	) -> Pin<Box<dyn Future<Output = Result<(), Error>> + Send>> {
		match self.client.block(&block_id) {
			Ok(Some(block)) => {
				let mut buf = Vec::new();
				1u64.encode_to(&mut buf);
				block.encode_to(&mut buf);
				let reader = std::io::Cursor::new(buf);
				self.import_blocks(reader, true)
			}
			Ok(None) => Box::pin(future::err("Unknown block".into())),
			Err(e) => Box::pin(future::err(format!("Error reading block: {:?}", e).into())),
		}
	}
}
