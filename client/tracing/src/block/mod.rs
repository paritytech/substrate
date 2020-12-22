// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Utilities for tracing block execution

use std::sync::Arc;
use parking_lot::Mutex;
use tracing::{Dispatch, dispatcher};
use tracing_subscriber::{
	FmtSubscriber,
	layer::SubscriberExt,
};

use sp_tracing::std_types::Traces;
use sc_client_api::{BlockBackend, BlockchainEvents, ExecutorProvider, ProofProvider, backend::{Backend, StorageProvider}};
use sp_api::{Core, Metadata, ProvideRuntimeApi, CallApiAt};
use sp_blockchain::{HeaderMetadata, HeaderBackend};
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header},
};

use crate::{TraceHandler, ProfilingLayer};
use std::marker::PhantomData;

pub struct BlockExecutor<BE, Block: BlockT, Client> {
	client: Arc<Client>,
	block: Block::Hash,
	_phantom: PhantomData<(BE, Block)>,
}

impl<BE, Block, Client> BlockExecutor<BE, Block, Client>
	where
		Block: BlockT + 'static,
		BE: Backend<Block> + 'static,
		Client: ExecutorProvider<Block> + StorageProvider<Block, BE> + ProofProvider<Block> + HeaderBackend<Block>
		+ BlockBackend<Block> + HeaderMetadata<Block, Error=sp_blockchain::Error> + BlockchainEvents<Block>
		+ CallApiAt<Block, Error=sp_blockchain::Error> + ProvideRuntimeApi<Block>
		+ Send + Sync + 'static,
		Client::Api: Metadata<Block, Error=sp_blockchain::Error>,
{
	pub fn new(client: Arc<Client>, block: Block::Hash) -> Self{
		Self { client, block, _phantom: PhantomData }
	}

	pub fn trace_block(self) -> Traces {
		let traces = Arc::new(Mutex::new(Traces::default()));
		let tracer = StorageTracer {
			traces: traces.clone(),
		};
		let profiling_layer = ProfilingLayer::new_with_handler(Box::new(tracer), "pallet,frame,state");
		let sub = FmtSubscriber::builder()
			.with_writer(|| std::io::sink())
			.finish()
			.with(profiling_layer);
		let dispatch = Dispatch::new(sub);
		dispatcher::with_default(&dispatch, || {
			let id = BlockId::Hash(self.block);
			let extrinsics = self.client.block_body(&id).expect("Invalid block id").expect("No extrinsics");
			let mut header = self.client.header(id).expect("Invalid block id").expect("No header");
			// Pop digest else: "Error executing block: Execution(RuntimePanicked(\"assertion failed: `(left == right)`\\n  left: `2`,\\n right: `1`: Number of digest items must match that calculated.\"
			header.digest_mut().pop();
			let parent_hash = header.parent_hash();
			let parent_id = BlockId::Hash(*parent_hash);
			let block = Block::new(header, extrinsics);

			match self.client.runtime_api().execute_block(&parent_id, block) {
				Err(e) => log::error!("Error executing block: {:?}", e),
				_ => (),
			}
		});
		drop(dispatch);
		Arc::try_unwrap(traces).expect("").into_inner()
	}
}

struct StorageTracer {
	traces: Arc<Mutex<Traces>>,
}

impl TraceHandler for StorageTracer {
	fn handle_span(&self, span: crate::SpanDatum) {
		self.traces.lock().spans.push(span.into());
	}

	fn handle_event(&self, event: crate::TraceEvent) {
		self.traces.lock().events.push(event.into());
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn test_state_trace() {}
}
