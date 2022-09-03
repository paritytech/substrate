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

use std::{
	collections::HashMap,
	sync::{
		atomic::{AtomicU64, Ordering},
		Arc,
	},
	time::Instant,
};

use parking_lot::Mutex;
use tracing::{
	dispatcher,
	span::{Attributes, Id, Record},
	Dispatch, Level, Subscriber,
};

use crate::{SpanDatum, TraceEvent, Values};
use sc_client_api::BlockBackend;
use sc_rpc_server::RPC_MAX_PAYLOAD_DEFAULT;
use sp_api::{Core, Encode, Metadata, ProvideRuntimeApi};
use sp_blockchain::HeaderBackend;
use sp_core::hexdisplay::HexDisplay;
use sp_rpc::tracing::{BlockTrace, Span, TraceBlockResponse, TraceError};
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header},
};
use sp_tracing::{WASM_NAME_KEY, WASM_TARGET_KEY, WASM_TRACE_IDENTIFIER};

// Heuristic for average event size in bytes.
const AVG_EVENT: usize = 600 * 8;
// Heuristic for average span size in bytes.
const AVG_SPAN: usize = 100 * 8;
// Estimate of the max base RPC payload size when the Id is bound as a u64. If strings
// are used for the RPC Id this may need to be adjusted. Note: The base payload
// does not include the RPC result.
//
// The estimate is based on the JSON-RPC response message which has the following format:
// `{"jsonrpc":"2.0","result":[],"id":18446744073709551615}`.
//
// We care about the total size of the payload because jsonrpc-server will simply ignore
// messages larger than `sc_rpc_server::MAX_PAYLOAD` and the caller will not get any
// response.
const BASE_PAYLOAD: usize = 100;
// Default to only pallet, frame support and state related traces
const DEFAULT_TARGETS: &str = "pallet,frame,state";
const TRACE_TARGET: &str = "block_trace";
// The name of a field required for all events.
const REQUIRED_EVENT_FIELD: &str = "method";
const MEGABYTE: usize = 1024 * 1024;

/// Tracing Block Result type alias
pub type TraceBlockResult<T> = Result<T, Error>;

/// Tracing Block error
#[derive(Debug, thiserror::Error)]
#[allow(missing_docs)]
#[non_exhaustive]
pub enum Error {
	#[error("Invalid block Id: {0}")]
	InvalidBlockId(#[from] sp_blockchain::Error),
	#[error("Missing block component: {0}")]
	MissingBlockComponent(String),
	#[error("Dispatch error: {0}")]
	Dispatch(String),
}

struct BlockSubscriber {
	targets: Vec<(String, Level)>,
	next_id: AtomicU64,
	spans: Mutex<HashMap<Id, SpanDatum>>,
	events: Mutex<Vec<TraceEvent>>,
}

impl BlockSubscriber {
	fn new(targets: &str) -> Self {
		let next_id = AtomicU64::new(1);
		let mut targets: Vec<_> = targets.split(',').map(crate::parse_target).collect();
		// Ensure that WASM traces are always enabled
		// Filtering happens when decoding the actual target / level
		targets.push((WASM_TRACE_IDENTIFIER.to_owned(), Level::TRACE));
		BlockSubscriber {
			targets,
			next_id,
			spans: Mutex::new(HashMap::new()),
			events: Mutex::new(Vec::new()),
		}
	}
}

impl Subscriber for BlockSubscriber {
	fn enabled(&self, metadata: &tracing::Metadata<'_>) -> bool {
		if !metadata.is_span() && metadata.fields().field(REQUIRED_EVENT_FIELD).is_none() {
			return false
		}
		for (target, level) in &self.targets {
			if metadata.level() <= level && metadata.target().starts_with(target) {
				return true
			}
		}
		false
	}

	fn new_span(&self, attrs: &Attributes<'_>) -> Id {
		let id = Id::from_u64(self.next_id.fetch_add(1, Ordering::Relaxed));
		let mut values = Values::default();
		attrs.record(&mut values);
		let parent_id = attrs.parent().cloned();
		let span = SpanDatum {
			id: id.clone(),
			parent_id,
			name: attrs.metadata().name().to_owned(),
			target: attrs.metadata().target().to_owned(),
			level: *attrs.metadata().level(),
			line: attrs.metadata().line().unwrap_or(0),
			start_time: Instant::now(),
			values,
			overall_time: Default::default(),
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
		unimplemented!("record_follows_from is not implemented");
	}

	fn event(&self, event: &tracing::Event<'_>) {
		let mut values = crate::Values::default();
		event.record(&mut values);
		let parent_id = event.parent().cloned();
		let trace_event = TraceEvent {
			name: event.metadata().name().to_owned(),
			target: event.metadata().target().to_owned(),
			level: *event.metadata().level(),
			values,
			parent_id,
		};
		self.events.lock().push(trace_event);
	}

	fn enter(&self, _id: &Id) {}

	fn exit(&self, _span: &Id) {}
}

/// Holds a reference to the client in order to execute the given block.
/// Records spans & events for the supplied targets (eg. "pallet,frame,state") and
/// only records events with the specified hex encoded storage key prefixes.
/// Note: if `targets` or `storage_keys` is an empty string then nothing is
/// filtered out.
pub struct BlockExecutor<Block: BlockT, Client> {
	client: Arc<Client>,
	block: Block::Hash,
	targets: Option<String>,
	storage_keys: Option<String>,
	methods: Option<String>,
	rpc_max_payload: usize,
}

impl<Block, Client> BlockExecutor<Block, Client>
where
	Block: BlockT + 'static,
	Client: HeaderBackend<Block>
		+ BlockBackend<Block>
		+ ProvideRuntimeApi<Block>
		+ Send
		+ Sync
		+ 'static,
	Client::Api: Metadata<Block>,
{
	/// Create a new `BlockExecutor`
	pub fn new(
		client: Arc<Client>,
		block: Block::Hash,
		targets: Option<String>,
		storage_keys: Option<String>,
		methods: Option<String>,
		rpc_max_payload: Option<usize>,
	) -> Self {
		let rpc_max_payload = rpc_max_payload
			.map(|mb| mb.saturating_mul(MEGABYTE))
			.unwrap_or(RPC_MAX_PAYLOAD_DEFAULT);
		Self { client, block, targets, storage_keys, methods, rpc_max_payload }
	}

	/// Execute block, record all spans and events belonging to `Self::targets`
	/// and filter out events which do not have keys starting with one of the
	/// prefixes in `Self::storage_keys`.
	pub fn trace_block(&self) -> TraceBlockResult<TraceBlockResponse> {
		tracing::debug!(target: "state_tracing", "Tracing block: {}", self.block);
		// Prepare the block
		let id = BlockId::Hash(self.block);
		let mut header = self
			.client
			.header(id)
			.map_err(Error::InvalidBlockId)?
			.ok_or_else(|| Error::MissingBlockComponent("Header not found".to_string()))?;
		let extrinsics = self
			.client
			.block_body(&id)
			.map_err(Error::InvalidBlockId)?
			.ok_or_else(|| Error::MissingBlockComponent("Extrinsics not found".to_string()))?;
		tracing::debug!(target: "state_tracing", "Found {} extrinsics", extrinsics.len());
		let parent_hash = *header.parent_hash();
		let parent_id = BlockId::Hash(parent_hash);
		// Remove all `Seal`s as they are added by the consensus engines after building the block.
		// On import they are normally removed by the consensus engine.
		header.digest_mut().logs.retain(|d| d.as_seal().is_none());
		let block = Block::new(header, extrinsics);

		let targets = if let Some(t) = &self.targets { t } else { DEFAULT_TARGETS };
		let block_subscriber = BlockSubscriber::new(targets);
		let dispatch = Dispatch::new(block_subscriber);

		{
			let dispatcher_span = tracing::debug_span!(
				target: "state_tracing",
				"execute_block",
				extrinsics_len = block.extrinsics().len(),
			);
			let _guard = dispatcher_span.enter();
			if let Err(e) = dispatcher::with_default(&dispatch, || {
				let span = tracing::info_span!(target: TRACE_TARGET, "trace_block");
				let _enter = span.enter();
				self.client.runtime_api().execute_block(&parent_id, block)
			}) {
				return Err(Error::Dispatch(format!(
					"Failed to collect traces and execute block: {}",
					e
				)))
			}
		}

		let block_subscriber = dispatch.downcast_ref::<BlockSubscriber>().ok_or_else(|| {
			Error::Dispatch(
				"Cannot downcast Dispatch to BlockSubscriber after tracing block".to_string(),
			)
		})?;
		let spans: Vec<_> = block_subscriber
			.spans
			.lock()
			.drain()
			// Patch wasm identifiers
			.filter_map(|(_, s)| patch_and_filter(s, targets))
			.collect();
		let events: Vec<_> = block_subscriber
			.events
			.lock()
			.drain(..)
			.filter(|e| {
				self.storage_keys
					.as_ref()
					.map(|keys| event_values_filter(e, "key", keys))
					.unwrap_or(false)
			})
			.filter(|e| {
				self.methods
					.as_ref()
					.map(|methods| event_values_filter(e, "method", methods))
					.unwrap_or(false)
			})
			.map(|s| s.into())
			.collect();
		tracing::debug!(target: "state_tracing", "Captured {} spans and {} events", spans.len(), events.len());

		let approx_payload_size = BASE_PAYLOAD + events.len() * AVG_EVENT + spans.len() * AVG_SPAN;
		let response = if approx_payload_size > self.rpc_max_payload {
			TraceBlockResponse::TraceError(TraceError {
				error: "Payload likely exceeds max payload size of RPC server.".to_string(),
			})
		} else {
			TraceBlockResponse::BlockTrace(BlockTrace {
				block_hash: block_id_as_string(id),
				parent_hash: block_id_as_string(parent_id),
				tracing_targets: targets.to_string(),
				storage_keys: self.storage_keys.clone().unwrap_or_default(),
				methods: self.methods.clone().unwrap_or_default(),
				spans,
				events,
			})
		};

		Ok(response)
	}
}

fn event_values_filter(event: &TraceEvent, filter_kind: &str, values: &str) -> bool {
	event
		.values
		.string_values
		.get(filter_kind)
		.map(|value| check_target(values, value, &event.level))
		.unwrap_or(false)
}

/// Filter out spans that do not match our targets and if the span is from WASM update its `name`
/// and `target` fields to the WASM values for those fields.
// The `tracing` crate requires trace metadata to be static. This does not work for wasm code in
// substrate, as it is regularly updated with new code from on-chain events. The workaround for this
// is for substrate's WASM tracing wrappers to put the `name` and `target` data in the `values` map
// (normally they would be in the static metadata assembled at compile time). Here, if a special
// WASM `name` or `target` key is found in the `values` we remove it and put the key value pair in
// the span's metadata, making it consistent with spans that come from native code.
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
			return None
		}
	}
	Some(span.into())
}

/// Check if a `target` matches any `targets` by prefix
fn check_target(targets: &str, target: &str, level: &Level) -> bool {
	for (t, l) in targets.split(',').map(crate::parse_target) {
		if target.starts_with(t.as_str()) && level <= &l {
			return true
		}
	}
	false
}

fn block_id_as_string<T: BlockT>(block_id: BlockId<T>) -> String {
	match block_id {
		BlockId::Hash(h) => HexDisplay::from(&h.encode()).to_string(),
		BlockId::Number(n) => HexDisplay::from(&n.encode()).to_string(),
	}
}
