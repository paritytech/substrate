// Copyright 2021 Parity Technologies (UK) Ltd.
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

use std::{collections::HashMap, sync::{Arc, atomic::{AtomicU64, Ordering}}};

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
use sp_rpc::tracing::{BlockTrace, Span, Event, Values};
use sp_tracing::{WASM_NAME_KEY, WASM_TARGET_KEY, WASM_TRACE_IDENTIFIER};

use tracing_core::{Level, span::{Attributes, Record, Id}};
use wasm_timer::Instant;


// Default to only runtime and state related traces
const DEFAULT_TARGETS: &'static str = "pallet,frame,sp_io::storage=debug";
const TRACE_TARGET: &'static str = "block_trace";

struct BlockSubscriber {
	targets: Vec<(String, Level)>,
	next_id: AtomicU64,
	current_span: CurrentSpan,
	spans: Mutex<HashMap<Id, Span>>,
	events: Mutex<Vec<Event>>,
	timestamp: Instant,
}

impl BlockSubscriber {
	fn new(
		targets: &str,
		spans: Mutex<HashMap<Id, Span>>,
		events: Mutex<Vec<Event>>,
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
			timestamp: Instant::now(),
		}
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
		let id = self.next_id.fetch_add(1, Ordering::Relaxed);
		let mut values = Values::default();
		attrs.record(&mut values);
		let parent_id = attrs.parent()
			.map(|pid| pid.into_u64())
			.or_else(|| self.current_span.id().map(|x| x.into_u64()));
		let span = Span {
			id,
			parent_id,
			name: attrs.metadata().name().to_owned(),
			target: attrs.metadata().target().to_owned(),
			level: *attrs.metadata().level(),
			line: attrs.metadata().line().unwrap_or(0),
			entered: vec![],
			exited: vec![],
			values: Values::default(),
		};
		let id = Id::from_u64(id);
		self.spans.lock().insert(id.clone(), span);
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

	fn event(&self, event: &tracing_core::Event<'_>) {
		let mut values = crate::Values::default();
		event.record(&mut values);
		let parent_id = event.parent()
			.map(|pid| pid.into_u64())
			.or_else(|| self.current_span.id().map(|x| x.into_u64()));
		let trace_event = Event {
			name: event.metadata().name().to_owned(),
			target: event.metadata().target().to_owned(),
			level: *event.metadata().level(),
			rel_timestamp: Instant::now() - self.timestamp,
			values: values.into(),
			parent_id,
		};
		self.events.lock().push(trace_event);
	}

	fn enter(&self, id: &Id) {
		self.current_span.enter(id.clone());
		let mut span_data = self.spans.lock();
		if let Some(span) = span_data.get_mut(&id) {
			span.entered.push(Instant::now() - self.timestamp);
		}
	}

	fn exit(&self, span: &Id) {
		if let Some(s) = self.spans.lock().get_mut(span) {
			self.current_span.exit();
			s.exited.push(Instant::now() - self.timestamp)
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
			.ok_or("Header not found".to_string())?;
		let parent_hash = header.parent_hash().clone();
		let parent_id = BlockId::Hash(parent_hash.clone());
		// Pop digest else RuntimePanic due to: 'Number of digest items must match that calculated.'
		header.digest_mut().pop();
		let block = Block::new(header, extrinsics);

		let targets = if let Some(t) = &self.targets { t } else { DEFAULT_TARGETS };
		let spans = Mutex::new(HashMap::new());
		let events = Mutex::new(Vec::new());
		let sub = BlockSubscriber::new(targets, spans, events);
		let dispatch = Dispatch::new(sub);

		if let Err(e) = dispatcher::with_default(&dispatch, || {
			let span = tracing::info_span!(
				target: TRACE_TARGET,
				"trace_block",
			);
			let _enter = span.enter();
			self.client.runtime_api().execute_block(&parent_id, block)
		}) {
			return Err(format!("Error executing block: {:?}", e));
		}
		let sub = dispatch.downcast_ref::<BlockSubscriber>()
			.ok_or("Cannot downcast Dispatch to BlockSubscriber after tracing block")?;
		let mut spans: Vec<Span> = sub.spans
			.lock()
			.drain()
			.map(|(_, s)| s.into())
			.into_iter()
			// First filter out any spans that were never entered
			.filter(|s: &Span| !s.entered.is_empty())
			// Patch wasm identifiers
			.filter_map(|s| patch_and_filter(s, targets))
			.collect();
		spans.sort_by(|a, b| a.entered[0].cmp(&b.entered[0]));

		let events = sub.events.lock().drain(..).map(|s| s.into()).collect();

		let block_traces = BlockTrace {
			block_hash: id.to_string(),
			parent_hash: parent_id.to_string(),
			tracing_targets: targets.to_string(),
			spans,
			events,
		};
		Ok(block_traces)
	}
}

fn patch_and_filter(mut span: Span, targets: &str) -> Option<Span> {
	if span.name == WASM_TRACE_IDENTIFIER {
		span.values.bool_values.insert("wasm".to_owned(), true);
		if let Some(n) = span.values.string_values.remove(WASM_NAME_KEY) {
			span.name = n;
		}
		if let Some(t) = span.values.string_values.remove(WASM_TARGET_KEY) {
			span.target = t;
		}
		if !check_target(targets, &span.target, &span.level) {
			return None;
		}
	}
	Some(span)
}

fn check_target(targets: &str, target: &str, level: &Level) -> bool {
	for (t, l) in targets.split(',').map(|s| crate::parse_target(s)) {
		if target.starts_with(t.as_str()) && level <= &l {
			return true;
		}
	}
	false
}
