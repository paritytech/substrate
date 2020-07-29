// Copyright 2020 Parity Technologies (UK) Ltd.
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

use crate::types::{
	WasmMetadata, WasmAttributes, WasmRecord, WasmEvent
};

use sp_runtime_interface::runtime_interface;

pub trait TracingSubscriber: Send + Sync {
	fn enabled(&self, metadata: WasmMetadata) -> bool;
	fn new_span(&self, attrs: WasmAttributes) -> u64;
	fn record(&self, span: u64, values: WasmRecord);
	fn event(&self, event: WasmEvent);
	fn enter(&self, span: u64);
	fn exit(&self, span: u64);
}

/// Interface that provides tracing functions
// #[runtime_interface(wasm_only, no_tracing)]
#[runtime_interface]
pub trait WasmTracing {
	fn enabled(&mut self, metadata: WasmMetadata) -> bool {
		crate::get_tracing_subscriber().map(|t|{
			t.enabled(metadata)
		}).unwrap_or(false)
	}
	fn new_span(&mut self, span: WasmAttributes) -> u64 {
		crate::get_tracing_subscriber().map(|t|{
			t.new_span(span)
		}).unwrap_or(0)
	}
	fn record(&mut self, span: u64, values: WasmRecord) {
		crate::get_tracing_subscriber().map(|t|{
			t.record(span, values)
		});
	}
	fn event(&mut self, event: WasmEvent) {
		crate::get_tracing_subscriber().map(|t|{
			t.event(event)
		});
	}
	fn enter(&mut self, span: u64) {
		crate::get_tracing_subscriber().map(|t|{
			t.enter(span)
		});
	}
	fn exit(&mut self, span: u64) {
		crate::get_tracing_subscriber().map(|t|{
			t.exit(span)
		});
	}
}