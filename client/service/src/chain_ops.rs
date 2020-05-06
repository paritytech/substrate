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
use sc_chain_spec::ChainSpec;
use log::{warn, info};
use futures::{future, prelude::*, task::{Context, Poll}};
use sp_runtime::traits::{
	Block as BlockT, NumberFor, One, Zero, Header, SaturatedConversion, MaybeSerializeDeserialize,
};
use futures::stream::Stream;
use sp_runtime::generic::{BlockId, SignedBlock};
use codec::{Decode, Encode, IoReader as CodecIoReader};
use crate::client::{Client, LocalCallExecutor};
use sp_consensus::{
	BlockOrigin,
	import_queue::{IncomingBlock, Link, BlockImportError, BlockImportResult, ImportQueue},
};
use sc_executor::{NativeExecutor, NativeExecutionDispatch};
use sp_core::storage::{StorageKey, well_known_keys, ChildInfo, Storage, StorageChild, StorageMap};
use sc_client_api::{StorageProvider, BlockBackend, UsageProvider};

use std::{io::{Read, Write, Seek}, pin::Pin, collections::HashMap};
use serde_json::{de::IoRead as JsonIoRead, Deserializer, StreamDeserializer};

/// Build a chain spec json
pub fn build_spec(spec: &dyn ChainSpec, raw: bool) -> error::Result<String> {
	spec.as_json(raw).map_err(Into::into)
}

/// Helper enum that wraps either a binary decoder (from parity-scale-codec), or a JSON decoder (from serde_json).
/// Implements the Stream Trait, calling `poll_next()` will decode the next SignedBlock and return it.
enum BlockStream<R, B> 
where
	R: std::io::Read + std::io::Seek,
{
	Binary {
		// Total number of blocks we are expecting to decode.
		count: u64,
		// Number of blocks we have decoded thus far.
		read_block_count: u64,
		// Reader to the data, used for decoding new blocks.
		reader: CodecIoReader<R>,
	},
	Json {
		// Nubmer of blocks we have decoded thus far.
		read_block_count: u64,
		// Stream to the data, used for decoding new blocks.
		reader: StreamDeserializer<'static, JsonIoRead<R>, SignedBlock<B>>,
	},
}

impl<R, B> Unpin for BlockStream<R, B> 
where
	R: Read + Seek
{}

impl<R, B> BlockStream<R, B>
	where
		R: Read + Seek + 'static,
		B: BlockT + MaybeSerializeDeserialize,
	{
	fn new(input: R, binary: bool) -> Result<Self, String> {
		if binary {
			let mut reader = CodecIoReader(input);
			// If the file is encoded in binary format, it is expected to first specify the number
			// of blocks that are going to be decoded. We read it and add it to our enum struct.
			let count: u64 = Decode::decode(&mut reader).map_err(|e| format!("Failed to decode the number of blocks: {:?}", e))?;
			Ok(BlockStream::Binary {
				count,
				read_block_count: 0,
				reader,
			})
		} else {
			let stream_deser  = Deserializer::from_reader(input)
				.into_iter::<SignedBlock<B>>();
			Ok(BlockStream::Json {
				reader: stream_deser,
				read_block_count: 0,
			})
		}
	}

	/// Returns the number of blocks read thus far.
	fn read_block_count(&self) -> u64 {
		match self {
			BlockStream::Binary { read_block_count, .. } | BlockStream::Json { read_block_count, .. } => *read_block_count,
		}
	}

	/// Returns the total number of blocks to be imported, if possible.
	fn count(&self) -> Option<u64> {
		match self {
			BlockStream::Binary { count, ..} => Some(*count),
			BlockStream::Json {..}=> None
		}
	}
}

impl<R, B> Stream for BlockStream<R, B> 
	where
		R: Read + Seek + 'static,
		B: BlockT + MaybeSerializeDeserialize,
	{
	type Item = Result<SignedBlock<B>, String>;

	/// Returns Poll::Ready(None) if every block have been read,
	/// else returns Poll::Ready(Some(block)), block being a result of decoding a signed block.
	fn poll_next(self: Pin<&mut Self>, _cx: &mut Context) -> Poll<Option<Self::Item>> {
		match Pin::get_mut(self) {
			BlockStream::Binary { count, read_block_count, reader } => {
				if read_block_count < count {
					let block_result: Result<SignedBlock::<B>, _> =  SignedBlock::<B>::decode(reader)
						.map_err(|e| e.to_string());
					*read_block_count += 1;
					Poll::Ready(Some(block_result))
				} else {
					// `read_block_count` == `count` so we've read enough blocks.
					Poll::Ready(None)
				}
			}
			BlockStream::Json { reader, read_block_count } => {
				match reader.next() {
					Some(block) => {
						*read_block_count += 1;
						Poll::Ready(Some(block.map_err(|e| e.to_string())))
					}
					None => {
						// We've reached the end of the iterator.
						Poll::Ready(None)
					}
				}
			}
		}
	}
}

/// Imports the SignedBlock to the queue.
fn import_block_to_queue<TBl, TImpQu>(signed_block: SignedBlock<TBl>, queue: &mut TImpQu, force: bool)
where
	TBl: BlockT + MaybeSerializeDeserialize,
	TImpQu: 'static + ImportQueue<TBl>,
{
	let (header, extrinsics) = signed_block.block.deconstruct();
	let hash = header.hash();
	// import queue handles verification and importing it into the client.
	queue.import_blocks(BlockOrigin::File, vec![
		IncomingBlock::<TBl> {
			hash,
			header: Some(header),
			body: Some(extrinsics),
			justification: signed_block.justification,
			origin: None,
			allow_missing_state: false,
			import_existing: force,
		}
	]);
}

/// Returns true if we have imported every block we were supposed to import, else returns false.
fn importing_is_done(count: Option<u64>, read_block_count: u64, imported_blocks: u64) -> bool {
	if let Some(count) = count {
		imported_blocks >= count
	} else {
		imported_blocks >= read_block_count
	}
}

// Logs information regarding the current importing status.
fn log_importing_status_updates(count: Option<u64>, read_block_count: u64, blocks_before: u64, imported_blocks: u64) {
	// Notify every 1000 blocks to let the user know everything is running smoothly.
	if read_block_count % 1000 == 0 {
		info!(
			"#{} blocks were added to the queue",
			read_block_count
		);
	}

	// Notify every time we import an additional 1000 blocks.
	if imported_blocks / 1000 != blocks_before / 1000 {
		if let Some(count) = count {
			info!(
				"#{} blocks were imported (#{} left)",
				imported_blocks,
				count - imported_blocks
			)
		} else {
			info!(
				"{} blocks were imported, other are still being processed",
				imported_blocks,
			)
		}
	}
}

impl<
	TBl, TRtApi, TBackend,
	TExecDisp, TFchr, TSc, TImpQu, TFprb, TFpp,
	TExPool, TRpc, Backend
> ServiceBuilderCommand for ServiceBuilder<
	TBl, TRtApi,
	Client<TBackend, LocalCallExecutor<TBackend, NativeExecutor<TExecDisp>>, TBl, TRtApi>,
	TFchr, TSc, TImpQu, TFprb, TFpp, TExPool, TRpc, Backend
> where
	TBl: BlockT + MaybeSerializeDeserialize,
	TBackend: 'static + sc_client_api::backend::Backend<TBl> + Send,
	TExecDisp: 'static + NativeExecutionDispatch,
	TImpQu: 'static + ImportQueue<TBl>,
	TRtApi: 'static + Send + Sync,
	Self: Send + 'static,
{
	type Block = TBl;
	type NativeDispatch = TExecDisp;

	fn import_blocks(
		mut self,
		input: impl Read + Seek + Send + 'static,
		force: bool,
		binary: bool,
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

		let mut link = WaitLink::new();
		let block_stream_res: Result<BlockStream<_, Self::Block>, String> = BlockStream::new(input, binary);

		let mut block_stream;
		match block_stream_res {
			Ok(bs) => {block_stream = bs},
			Err(e) => {
				// We've encountered an error while creating the block stream 
				// so we can just return a future that returns an error.
				let err_import = future::poll_fn(move |_cx| {
					return std::task::Poll::Ready(Err(Error::Other(e.clone())))
				});
				return Box::pin(err_import)
			}
		};

		// Importing blocks is implemented as a future, because we want the operation to be
		// interruptible.
		//
		// Every time we read a block from the input or import a bunch of blocks from the import
		// queue, the `Future` re-schedules itself and returns `Poll::Pending`.
		// This makes it possible either to interleave other operations in-between the block imports,
		// or to stop the operation completely.
		let import = future::poll_fn(move |cx| {
			let client = &self.client;
			let queue = &mut self.import_queue;

			// Read blocks from the input.
			match Pin::new(&mut block_stream).poll_next(cx) {
				Poll::Ready(None) => {
					let read_block_count = block_stream.read_block_count();
					let count = block_stream.count();

					if importing_is_done(count, read_block_count, link.imported_blocks) {
						info!(
							"🎉 Imported {} blocks. Best: #{}",
							read_block_count, client.chain_info().best_number
						);
						return std::task::Poll::Ready(Ok(()))
					}
				},
				Poll::Ready(Some(block_result)) => {
					match block_result {
						Ok(signed_block) => import_block_to_queue(signed_block, queue, force),
						Err(e) => {
							let read_block_count = block_stream.read_block_count();
							warn!("Error reading block data at {}: {}", read_block_count, e);
							// We've encountered an error, we can stop here.
							return std::task::Poll::Ready(Ok(()));
						}
					}
				}
				Poll::Pending => unreachable!("BlockStream.poll_next() should never return Poll::Pending; qed")
			}

			let blocks_before = link.imported_blocks;
			queue.poll_actions(cx, &mut link);

			if link.has_error {
				info!(
					"Stopping after #{} blocks because of an error",
					link.imported_blocks,
				);
				// We've encountered an error, we can stop here.
				return std::task::Poll::Ready(Ok(()));
			}

			let read_block_count = block_stream.read_block_count();
			let count = block_stream.count();
			log_importing_status_updates(count, read_block_count, blocks_before, link.imported_blocks);


			cx.waker().wake_by_ref();
			std::task::Poll::Pending
		});
		Box::pin(import)
	}

	fn export_blocks(
		self,
		mut output: impl Write + 'static,
		from: NumberFor<TBl>,
		to: Option<NumberFor<TBl>>,
		binary: bool
	) -> Pin<Box<dyn Future<Output = Result<(), Error>>>> {
		let mut block = from;

		let last = match to {
			Some(v) if v.is_zero() => One::one(),
			Some(v) => v,
			None => self.client.chain_info().best_number,
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
			let client = &self.client;

			if last < block {
				return std::task::Poll::Ready(Err("Invalid block range specified".into()));
			}

			if !wrote_header {
				info!("Exporting blocks from #{} to #{}", block, last);
				if binary {
					let last_: u64 = last.saturated_into::<u64>();
					let block_: u64 = block.saturated_into::<u64>();
					let len: u64 = last_ - block_ + 1;
					output.write_all(&len.encode())?;
				}
				wrote_header = true;
			}

			match client.block(&BlockId::number(block))? {
				Some(block) => {
					if binary {
						output.write_all(&block.encode())?;
					} else {
						serde_json::to_writer(&mut output, &block)
							.map_err(|e| format!("Error writing JSON: {}", e))?;
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
				self.import_blocks(reader, true, true)
			}
			Ok(None) => Box::pin(future::err("Unknown block".into())),
			Err(e) => Box::pin(future::err(format!("Error reading block: {:?}", e).into())),
		}
	}

	fn export_raw_state(
		&self,
		block: Option<BlockId<Self::Block>>,
	) -> Result<Storage, Error> {
		let block = block.unwrap_or_else(
			|| BlockId::Hash(self.client.usage_info().chain.best_hash)
		);

		let empty_key = StorageKey(Vec::new());
		let mut top_storage = self.client.storage_pairs(&block, &empty_key)?;
		let mut children_default = HashMap::new();

		// Remove all default child storage roots from the top storage and collect the child storage
		// pairs.
		while let Some(pos) = top_storage
			.iter()
			.position(|(k, _)| k.0.starts_with(well_known_keys::DEFAULT_CHILD_STORAGE_KEY_PREFIX)) {
			let (key, _) = top_storage.swap_remove(pos);

			let key = StorageKey(
				key.0[well_known_keys::DEFAULT_CHILD_STORAGE_KEY_PREFIX.len()..].to_vec(),
			);
			let child_info = ChildInfo::new_default(&key.0);

			let keys = self.client.child_storage_keys(&block, &child_info, &empty_key)?;
			let mut pairs = StorageMap::new();
			keys.into_iter().try_for_each(|k| {
				if let Some(value) = self.client.child_storage(&block, &child_info, &k)? {
					pairs.insert(k.0, value.0);
				}

				Ok::<_, Error>(())
			})?;

			children_default.insert(key.0, StorageChild { child_info, data: pairs });
		}

		let top = top_storage.into_iter().map(|(k, v)| (k.0, v.0)).collect();
		Ok(Storage { top, children_default })
	}
}
