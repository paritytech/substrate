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
use std::time::Instant;

use parking_lot::Mutex;
use tracing::{Dispatch, dispatcher, Subscriber, Level, span::{Attributes, Record, Id}};
use tracing_subscriber::CurrentSpan;

use sc_client_api::BlockBackend;
use sp_api::{Core, Metadata, ProvideRuntimeApi, Encode};
use sp_blockchain::HeaderBackend;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header},
};
use sp_rpc::tracing::{BlockTrace, Span, TraceError, TraceBlockResponse};
use sp_tracing::{WASM_NAME_KEY, WASM_TARGET_KEY, WASM_TRACE_IDENTIFIER};
use sp_core::hexdisplay::HexDisplay;
use crate::{SpanDatum, TraceEvent, Values};

// Default to only pallet, frame support and state related traces
const DEFAULT_TARGETS: &'static str = "pallet,frame,state";
const TRACE_TARGET: &'static str = "block_trace";
// Default to only events with the key prefixes for :extrinsic_index & system::Account.
const DEFAULT_STORAGE_KEYS: &'static str =
	"3a65787472696e7369635f696e646578,26aa394eea5630e07c48ae0c9558cef7b99d880ec681799c0cf30e8886371da9";
/// Maximal payload accepted by RPC servers. // TODO maybe import from sc_rpc_server
const MAX_PAYLOAD: usize = 15 * 1024 * 1024;

struct BlockSubscriber {
	targets: Vec<(String, Level)>,
	next_id: AtomicU64,
	current_span: CurrentSpan,
	spans: Mutex<HashMap<Id, SpanDatum>>,
	events: Mutex<Vec<TraceEvent>>,
	timestamp: Instant,
}

impl BlockSubscriber {
	fn new(
		targets: &str,
		spans: Mutex<HashMap<Id, SpanDatum>>,
		events: Mutex<Vec<TraceEvent>>,
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
	fn enabled(&self, metadata: &tracing::Metadata<'_>) -> bool {
		for (target, level) in &self.targets {
			if metadata.target().starts_with(target.as_str()) && metadata.level() <= level {
				return true;
			}
		}
		false
	}

	fn new_span(&self, attrs: &Attributes<'_>) -> Id {
		let id = self.next_id.fetch_add(1, Ordering::Relaxed);
		let id = Id::from_u64(id);
		let mut values = Values::default();
		attrs.record(&mut values);
		let parent_id = attrs.parent().cloned()
			.or_else(|| self.current_span.id());
		let span = SpanDatum {
			id: id.clone(),
			parent_id,
			name: attrs.metadata().name().to_owned(),
			target: attrs.metadata().target().to_owned(),
			level: *attrs.metadata().level(),
			line: attrs.metadata().line().unwrap_or(0),
			start_time: Instant::now(),
			values,
			overall_time: Default::default()
		};

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

	fn event(&self, event: &tracing::Event<'_>) {
		let mut values = crate::Values::default();
		event.record(&mut values);
		let parent_id = event.parent().cloned()
			.or_else(|| self.current_span.id());
		let trace_event = TraceEvent {
			name: event.metadata().name().to_owned(),
			target: event.metadata().target().to_owned(),
			level: *event.metadata().level(),
			values: values.into(),
			parent_id,
		};
		self.events.lock().push(trace_event);
	}

	fn enter(&self, id: &Id) {
		self.current_span.enter(id.clone());
	}

	fn exit(&self, span: &Id) {
		if let Some(s) = self.spans.lock().get_mut(span) {
			self.current_span.exit();
		}
	}
}

/// Holds a reference to the client in order to execute the given block
/// and record traces for the supplied targets (eg. "pallet,frame,state")
pub struct BlockExecutor<Block: BlockT, Client> {
	client: Arc<Client>,
	block: Block::Hash,
	targets: Option<String>,
	storage_keys: Option<String>,
}

impl<Block, Client> BlockExecutor<Block, Client>
	where
		Block: BlockT + 'static,
		Client: HeaderBackend<Block> + BlockBackend<Block> + ProvideRuntimeApi<Block>
		+ Send + Sync + 'static,
		Client::Api: Metadata<Block>,
{
	/// Create a new `BlockExecutor`
	pub fn new(
		client: Arc<Client>,
		block: Block::Hash,
		targets: Option<String>,
		storage_keys: Option<String>,
	) -> Self {
		Self { client, block, targets, storage_keys }
	}

	/// Execute block, recording all spans and events belonging to `Self::targets`
	pub fn trace_block(&self) -> Result<TraceBlockResponse, String> {
		tracing::debug!(target: "state_tracing", "Tracing block: {}", self.block);

		// Prepare block
		let id = BlockId::Hash(self.block);
		let extrinsics = self.client.block_body(&id)
			.map_err(|e| format!("Invalid block id: {:?}", e))?
			.ok_or("Block not found".to_string())?;

		tracing::debug!(target: "state_tracing", "Found {} extrinsics", extrinsics.len());

		let mut header = self.client.header(id)
			.map_err(|e| format!("Invalid block id: {:?}", e))?
			.ok_or("Header not found".to_string())?;
		let parent_hash = header.parent_hash().clone();
		let parent_id = BlockId::Hash(parent_hash.clone());
		// Pop digest else RuntimePanic due to: 'Number of digest items must match that calculated.'
		header.digest_mut().pop();
		let block = Block::new(header, extrinsics);

		let targets = if let Some(t) = &self.targets { t } else { DEFAULT_TARGETS };
		let storage_keys = if let Some(s) = &self.storage_keys {
			s
		} else {
			DEFAULT_STORAGE_KEYS
		};
		let spans = Mutex::new(HashMap::new());
		let events = Mutex::new(Vec::new());
		let block_subscriber = BlockSubscriber::new(targets, spans, events);
		let dispatch = Dispatch::new(block_subscriber);

		{
			let dispatcher_span = tracing::debug_span!(target: "state_tracing",
				"execute_block", extrinsics_len = block.extrinsics().len());
			let _guard = dispatcher_span.enter();
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
		}

		let block_subscriber = dispatch.downcast_ref::<BlockSubscriber>()
			.ok_or("Cannot downcast Dispatch to BlockSubscriber after tracing block")?;
		let mut span_data: Vec<SpanDatum> = block_subscriber.spans
			.lock()
			.drain()
			.map(|(_, s)| SpanDatum::from(s))
			.collect::<Vec<SpanDatum>>();

		// Is there a way to do this sort without collecting twice? My only idea was to add start_time
		// into `Span` - zeke
		span_data.sort_by(|a, b| a.start_time.cmp(&b.start_time));

		let spans: Vec<Span> = span_data
			.into_iter()
			// Patch wasm identifiers
			.filter_map(|s| patch_and_filter(s, targets))
			.collect();

		let events: Vec<_> = block_subscriber.events
			.lock()
			.drain(..)
			.filter(|e| event_key_filter(e, storage_keys))
			.map(|s| s.into())
			.collect();

		tracing::debug!(target: "state_tracing", "Captured {} spans and {} events", spans.len(), events.len());

		let block_trace = BlockTrace {
			block_hash: block_id_as_string(id),
			parent_hash: block_id_as_string(parent_id),
			tracing_targets: targets.to_string(),
			storage_keys: storage_keys.to_string(),
			spans,
			events,
		};

		let block_trace_size = serde_json::to_vec(&block_trace)
			.map_err(|_| "Failed to serialize payload".to_string())?
			.len();
		let response = if block_trace_size  > MAX_PAYLOAD {
			TraceBlockResponse::TraceError(TraceError {
				error:
					format!(
						"Payload was {} bytes; it must be less than {} bytes",
						block_trace_size,
						MAX_PAYLOAD
					)
			})
		} else {
			TraceBlockResponse::BlockTrace(block_trace)
		};

		Ok(response)
	}
}

fn event_key_filter(event: &TraceEvent, storage_keys: &str) -> bool {
	event.values.string_values.get("key")
		.and_then(|key| Some(check_target(storage_keys, key, &event.level)))
		.unwrap_or(false)
}

fn patch_and_filter(mut span: SpanDatum, targets: &str) -> Option<Span> {
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
	Some(span.into())
}

fn check_target(targets: &str, target: &str, level: &Level) -> bool {
	for (t, l) in targets.split(',').map(|s| crate::parse_target(s)) {
		if target.starts_with(t.as_str()) && level <= &l {
			return true;
		}
	}
	false
}

fn block_id_as_string<T: BlockT>(block_id: BlockId<T>) -> String {
	 match block_id {
		BlockId::Hash(h) => HexDisplay::from(&h.encode()).to_string(),
		BlockId::Number(n) =>  HexDisplay::from(&n.encode()).to_string()
	}
}