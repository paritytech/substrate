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

use parking_lot::Mutex;
// use serde::Serialize;
use tracing::{Dispatch, dispatcher};
use tracing_subscriber::{
	FmtSubscriber,
	layer::SubscriberExt,
};
use crate::{TraceHandler, ProfilingLayer};
use sp_tracing::std_types::Traces;
use std::sync::Arc;

pub fn trace_block<Block>(targets: String, block: Block::Hash) -> Traces
	where
		Block: sp_runtime::traits::Block + 'static,
{
	let traces = Arc::new(Mutex::new(Traces::default()));
	let tracer = StorageTracer {
		traces: traces.clone(),
	};
	let profiling_layer = ProfilingLayer::new_with_handler(Box::new(tracer), &targets);
	let sub = FmtSubscriber::builder()
		.with_writer(|| std::io::sink())
		.finish()
		.with(profiling_layer);
	let dispatch = Dispatch::new(sub);
	dispatcher::with_default(&dispatch, || {
		//TODO Execute block, capturing traces
	});
	drop(dispatch);
	Arc::try_unwrap(traces).expect("").into_inner()
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
	fn test_state_trace() {

	}
}
