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
use tracing_subscriber::{FmtSubscriber, layer::SubscriberExt, EnvFilter};

use sc_client_api::BlockBackend;
use sp_api::{Core, Metadata, ProvideRuntimeApi};
use sp_blockchain::HeaderBackend;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header},
};
use sp_rpc::tracing::BlockTrace;

use crate::{TraceHandler, ProfilingLayer};

// Default to only runtime and state related traces
const DEFAULT_TARGETS: &'static str = "pallet,frame,state";
const TRACE_TARGET: &'static str = "block_trace";

/// Holds a reference to the client in order to execute the given block
/// and record traces for the supplied targets (eg. "pallet,frame,state")
pub struct BlockExecutor<Block: BlockT, Client> {
	client: Arc<Client>,
	block: Block::Hash,
	targets: Option<String>
}

impl<Block, Client> BlockExecutor<Block, Client>
	where
		Block: BlockT + 'static,
		Client: HeaderBackend<Block> + BlockBackend<Block> + ProvideRuntimeApi<Block>
		+ Send + Sync + 'static,
		Client::Api: Metadata<Block, Error=sp_blockchain::Error>,
{
	/// Create a new `BlockExecutor`
	pub fn new(client: Arc<Client>, block: Block::Hash, targets: Option<String>) -> Self {
		Self { client, block, targets }
	}

	/// Execute block, recording all spans and events belonging to `Self::targets`
	pub fn trace_block(&self) -> Result<BlockTrace, String> {
		// Prepare block
		let id = BlockId::Hash(self.block);
		let extrinsics = self.client.block_body(&id)
			.map_err(|e| format!("Invalid block id: {:?}", e))?
			.ok_or("Block not found".to_string())?;
		let mut header = self.client.header(id)
			.map_err(|e| format!("Invalid block id: {:?}", e))?
			.ok_or("Block not found".to_string())?;
		let parent_hash = header.parent_hash().clone();
		let parent_id = BlockId::Hash(parent_hash.clone());
		// Pop digest else RuntimePanic due to: 'Number of digest items must match that calculated.'
		header.digest_mut().pop();
		let block = Block::new(header, extrinsics);

		let targets = if let Some(t) = &self.targets { t } else { DEFAULT_TARGETS };
		let block_traces = BlockTrace {
			block_hash: id.to_string(),
			parent_hash: parent_id.to_string(),
			tracing_targets: targets.to_string(),
			..Default::default()
		};
		let traces = Arc::new(Mutex::new(block_traces));
		let dispatch = create_dispatch(traces.clone(), targets)?;

		if let Err(e) = dispatcher::with_default(&dispatch, || {
			let span = tracing::info_span!(
				target: TRACE_TARGET,
				"trace_block"
			);
			let _enter = span.enter();
			self.client.runtime_api().execute_block(&parent_id, block)
		}) {
			return Err(format!("Error executing block: {:?}", e));
		}

		drop(dispatch);
		Ok(Arc::try_unwrap(traces).map_err(|_| "Unable to unwrap block traces".to_string())?.into_inner())
	}
}

struct StorageTracer {
	traces: Arc<Mutex<BlockTrace>>,
}

impl TraceHandler for StorageTracer {
	fn handle_span(&self, span: crate::SpanDatum) {
		self.traces.lock().spans.push(span.into());
	}

	fn handle_event(&self, event: crate::TraceEvent) {
		self.traces.lock().events.push(event.into());
	}
}

fn create_dispatch(traces: Arc<Mutex<BlockTrace>>, targets: &str) -> Result<Dispatch, String> {
	let tracer = StorageTracer {
		traces,
	};
	let filter = EnvFilter::try_new(targets)
		.map_err(|e| format!("{:?}", e))?
		.add_directive(
			TRACE_TARGET.parse().expect("TRACE_TARGET is valid; qed")
		);
	let profiling_layer = ProfilingLayer::new_with_handler(
		Box::new(tracer),
		targets,
	);
	let sub = FmtSubscriber::builder()
		.with_env_filter(filter)
		.with_writer(std::io::sink)
		.finish()
		.with(profiling_layer);
	Ok(Dispatch::new(sub))
}
