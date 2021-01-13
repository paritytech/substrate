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

use std::collections::HashMap;
use std::sync::{Arc};
use std::sync::atomic::{AtomicU64, Ordering};

use parking_lot::Mutex;
use tracing::{Dispatch, dispatcher, Subscriber};
use tracing_subscriber::CurrentSpan;

use sc_client_api::BlockBackend;
use sp_api::{Core, Metadata, ProvideRuntimeApi};
use sp_blockchain::HeaderBackend;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header},
};
use sp_rpc::tracing::{BlockTrace};
use sp_tracing::{WASM_NAME_KEY, WASM_TARGET_KEY, WASM_TRACE_IDENTIFIER};

use tracing_core::span::{Attributes, Record, Id};
use tracing_core::{Level, Event};
use std::time::{Duration, Instant};
use crate::{SpanDatum, TraceEvent};

// Default to only runtime and state related traces
const DEFAULT_TARGETS: &'static str = "pallet,frame,state";
const TRACE_TARGET: &'static str = "block_trace";

struct BlockSubscriber {
	targets: Vec<(String, Level)>,
	next_id: AtomicU64,
	current_span: CurrentSpan,
	spans: Arc<Mutex<HashMap<Id, SpanDatum>>>,
	events: Arc<Mutex<Vec<TraceEvent>>>,
}

impl BlockSubscriber {
	fn new(
		targets: &str,
		spans: Arc<Mutex<HashMap<Id, SpanDatum>>>,
		events: Arc<Mutex<Vec<TraceEvent>>>,
	) -> Self {
		let next_id = AtomicU64::new(1);
		let mut targets: Vec<_> = targets
			.split(',')
			.map(|s| crate::parse_target(s))
			.collect();
		// Ensure that WASM traces are always enabled
		// Filtering happens when decoding the actual target / level
		targets.push((WASM_TRACE_IDENTIFIER.to_owned(), Level::TRACE));
		BlockSubscriber {
			targets,
			next_id,
			current_span: CurrentSpan::default(),
			spans,
			events,
		}
	}

	fn check_target(&self, target: &str, level: &Level) -> bool {
		for t in &self.targets {
			if target.starts_with(t.0.as_str()) && level <= &t.1 {
				return true;
			}
		}
		false
	}
}

impl Subscriber for BlockSubscriber {
	fn enabled(&self, metadata: &tracing_core::Metadata<'_>) -> bool {
		for (target, level) in &self.targets {
			if metadata.target().starts_with(target.as_str()) && metadata.level() <= level {
				return true;
			}
		}
		false
	}

	fn new_span(&self, attrs: &Attributes<'_>) -> Id {
		let mut values = crate::Values::default();
		let id = self.next_id.fetch_add(1, Ordering::Relaxed);
		let id = Id::from_u64(id);
		attrs.record(&mut values);
		let span_datum = crate::SpanDatum {
			id: id.clone(),
			parent_id: attrs.parent().cloned().or_else(|| self.current_span.id()),
			name: attrs.metadata().name().to_owned(),
			target: attrs.metadata().target().to_owned(),
			level: *attrs.metadata().level(),
			line: attrs.metadata().line().unwrap_or(0),
			start_time: Instant::now(),
			overall_time: Duration::new(0, 0),
			values,
		};
		self.spans.lock().insert(id.clone(), span_datum);
		id
	}

	fn record(&self, span: &Id, values: &Record<'_>) {
		let mut span_data = self.spans.lock();
		if let Some(s) = span_data.get_mut(span) {
			values.record(&mut s.values);
		}
	}

	fn record_follows_from(&self, _span: &Id, _follows: &Id) {
		// Not currently used
	}

	fn event(&self, event: &Event<'_>) {
		let mut values = crate::Values::default();
		event.record(&mut values);
		let trace_event = TraceEvent {
			name: event.metadata().name(),
			target: event.metadata().target().to_owned(),
			level: *event.metadata().level(),
			values,
			parent_id: event.parent().cloned().or_else(|| self.current_span.id()),
		};
		self.events.lock().push(trace_event);
	}

	fn enter(&self, span: &Id) {
		self.current_span.enter(span.clone());
		let mut span_data = self.spans.lock();
		let start_time = Instant::now();
		if let Some(mut s) = span_data.get_mut(&span) {
			s.start_time = start_time;
		}
	}

	fn exit(&self, span: &Id) {
		let end_time = Instant::now();
		let span_datum = {
			let mut span_data = self.spans.lock();
			span_data.remove(&span)
		};

		if let Some(mut span_datum) = span_datum {
			self.current_span.exit();
			span_datum.overall_time += end_time - span_datum.start_time;
			if span_datum.name == WASM_TRACE_IDENTIFIER {
				span_datum.values.bool_values.insert("wasm".to_owned(), true);
				if let Some(n) = span_datum.values.string_values.remove(WASM_NAME_KEY) {
					span_datum.name = n;
				}
				if let Some(t) = span_datum.values.string_values.remove(WASM_TARGET_KEY) {
					span_datum.target = t;
				}
				if !self.check_target(&span_datum.target, &span_datum.level) {
					return;
				}
			}
			self.spans.lock().insert(span_datum.id.clone(), span_datum);
		}
	}
}

/// Holds a reference to the client in order to execute the given block
/// and record traces for the supplied targets (eg. "pallet,frame,state")
pub struct BlockExecutor<Block: BlockT, Client> {
	client: Arc<Client>,
	block: Block::Hash,
	targets: Option<String>,
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
		let spans = Arc::new(Mutex::new(HashMap::new()));
		let events = Arc::new(Mutex::new(Vec::new()));
		let sub = BlockSubscriber::new(targets, spans.clone(), events.clone());
		let dispatch = Dispatch::new(sub);

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
		let spans = Arc::try_unwrap(spans)
			.map_err(|_| "Unable to unwrap spans".to_string())?;
		let events = Arc::try_unwrap(events)
			.map_err(|_| "Unable to unwrap spans".to_string())?;
		let block_traces = BlockTrace {
			block_hash: id.to_string(),
			parent_hash: parent_id.to_string(),
			tracing_targets: targets.to_string(),
			spans: spans.into_inner().into_iter().map(|(_, s)| s.into()).collect(),
			events: events.into_inner().into_iter().map(|s| s.into()).collect(),
		};
		Ok(block_traces)
	}
}
