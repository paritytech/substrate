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

//! Proxy to allow entering tracing spans from wasm.
//!
//! Use `enter_span` and `exit_span` to surround the code that you wish to trace
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};

/// Used to identify a proxied WASM trace
pub const WASM_PROXY_ID: &'static str = "proxied_wasm_trace_id";
/// Used to extract the real `target` from the associated values of the span
pub const WASM_TARGET_KEY: &'static str = "proxied_wasm_target";
/// Used to extract the real `name` from the associated values of the span
pub const WASM_NAME_KEY: &'static str = "proxied_wasm_name";

// Ensure we don't use 0 for an id
static NEXT_ID: AtomicU64 = AtomicU64::new(1);

/// Create and enter a `tracing` Span, returning the span id,
/// which should be passed to `exit_span(id)` to signal that the span should exit.
// fn parameter identifiers should match the const values above
pub fn enter_span(proxied_wasm_target: &str, proxied_wasm_name: &str) -> u64 {
	let proxied_wasm_trace_id = next_id();
	tracing::event!(
		tracing::Level::INFO,
		proxied_wasm_target,
		proxied_wasm_name,
		proxied_wasm_trace_id,
		"proxy_enter_span"
	);
	proxied_wasm_trace_id
}

/// Exit a span by dropping it along with it's associated guard.
// fn parameter identifier should match the const value above
pub fn exit_span(proxied_wasm_trace_id: u64) {
	tracing::event!(
		tracing::Level::INFO,
		proxied_wasm_trace_id,
		"proxy_exit_span"
	);
}

/// Universal source for tracing span ids
pub fn next_id() -> u64 {
	NEXT_ID.fetch_add(1, Relaxed)
}