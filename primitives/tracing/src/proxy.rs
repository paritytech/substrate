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
use tracing::info_span;
use crate::proxied_span::ProxiedSpan;

/// Used to identify a proxied WASM trace
pub const WASM_TRACE_IDENTIFIER: &'static str = "WASM_TRACE";
/// Used to extract the real `target` from the associated values of the span
pub const WASM_TARGET_KEY: &'static str = "proxied_wasm_target";
/// Used to extract the real `name` from the associated values of the span
pub const WASM_NAME_KEY: &'static str = "proxied_wasm_name";

const MAX_SPANS_LEN: usize = 1000;

/// Requires a tracing::Subscriber to process span traces,
/// this is available when running with client (and relevant cli params).
pub struct TracingProxy {
	next_id: u64,
	spans: Vec<ProxiedSpan>,
}

impl Drop for TracingProxy {
	fn drop(&mut self) {
		if !self.spans.is_empty() {
			log::debug!(
				target: "tracing",
				"Dropping TracingProxy with {} un-exited spans, marking as not valid", self.spans.len()
			);
			while let Some(proxied_trace) = self.spans.pop() {
				proxied_trace.span().record("is_valid_trace", &false);
			}
		}
	}
}

impl TracingProxy {
	pub fn new() -> TracingProxy {
		TracingProxy {
			next_id: 0,
			spans: Vec::new(),
		}
	}
}

impl TracingProxy {
	/// Create and enter a `tracing` Span, returning the span id,
	/// which should be passed to `exit_span(id)` to signal that the span should exit.
	pub fn enter_span(&mut self, proxied_wasm_target: &str, proxied_wasm_name: &str) -> u64 {
		// The identifiers `proxied_wasm_target` and `proxied_wasm_name` must match their associated const,
		// WASM_TARGET_KEY and WASM_NAME_KEY.
		let span = Box::pin(
			info_span!(
				WASM_TRACE_IDENTIFIER,
				is_valid_trace = true,
				proxied_wasm_target,
				proxied_wasm_name
			)
		);
		self.next_id += 1;
		let proxied_trace = ProxiedSpan::enter_span(self.next_id, span);
		self.spans.push(proxied_trace);
		if self.spans.len() > MAX_SPANS_LEN {
			// This is to prevent unbounded growth of Vec and could mean one of the following:
			// 1. Too many nested spans, or MAX_SPANS_LEN is too low.
			// 2. Not correctly exiting spans due to misconfiguration / misuse
			log::warn!(
				target: "tracing",
				"TracingProxy MAX_SPANS_LEN exceeded, removing oldest span."
			);
			let proxied_trace = self.spans.remove(0);
			proxied_trace.span().record("is_valid_trace", &false);
		}
		self.next_id
	}

	/// Exit a span by dropping it along with it's associated guard.
	pub fn exit_span(&mut self, id: u64) {
		if self.spans.last().map(|proxied_trace| id > proxied_trace.id()).unwrap_or(true) {
			log::warn!(target: "tracing", "Span id not found in TracingProxy: {}", id);
			return;
		}
		let mut proxied_trace = self.spans.pop().expect("Just checked that there is an element to pop; qed");
		while id < proxied_trace.id() {
			log::warn!(
				target: "tracing",
				"TracingProxy Span ids not equal! id parameter given: {}, last span: {}",
				id,
				proxied_trace.id(),
			);
			proxied_trace.span().record("is_valid_trace", &false);
			if let Some(pt) = self.spans.pop() {
				proxied_trace = pt;
			} else {
				log::warn!(target: "tracing", "Span id not found in TracingProxy {}", id);
				return;
			}
		}
	}
}


#[cfg(test)]
mod tests {
	use super::*;

	fn create_spans(proxy: &mut TracingProxy, qty: usize) -> Vec<u64> {
		let mut spans = Vec::new();
		for n in 0..qty {
			spans.push(proxy.enter_span("target", &format!("{}", n)));
		}
		spans
	}

	#[test]
	fn max_spans_len_respected() {
		let mut proxy = TracingProxy::new();
		let _spans = create_spans(&mut proxy, MAX_SPANS_LEN + 10);
		assert_eq!(proxy.spans.len(), MAX_SPANS_LEN);
		// ensure oldest spans removed
		assert_eq!(proxy.spans[0].0, 11);
	}

	#[test]
	fn handles_span_exit_scenarios() {
		let mut proxy = TracingProxy::new();
		let _spans = create_spans(&mut proxy, 10);
		assert_eq!(proxy.spans.len(), 10);
		// exit span normally
		proxy.exit_span(10);
		assert_eq!(proxy.spans.len(), 9);
		// skip and exit outer span without exiting inner, id: 8 instead of 9
		proxy.exit_span(8);
		// should have also removed the inner span that was lost
		assert_eq!(proxy.spans.len(), 7);
		// try to exit span not held
		proxy.exit_span(9);
		assert_eq!(proxy.spans.len(), 7);
		// exit all spans
		proxy.exit_span(1);
		assert_eq!(proxy.spans.len(), 0);
	}
}
