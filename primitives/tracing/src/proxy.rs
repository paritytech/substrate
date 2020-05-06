use std::cell::RefCell;
use rental;

use crate::span_dispatch;

const MAX_SPANS_LEN: usize = 1000;

thread_local! {
	static PROXY: RefCell<TracingProxy> = RefCell::new(TracingProxy::new());
}

pub fn create_registered_span(target: &str, name: &str) -> u64 {
	PROXY.with(|proxy| proxy.borrow_mut().create_registered_span(target, name))
}

pub fn exit_span(id: u64) {
	PROXY.with(|proxy| proxy.borrow_mut().exit_span(id));
}

rental! {
	pub mod rent_span {
		#[rental]
		pub struct SpanAndGuard {
			span: Box<tracing::Span>,
			guard: tracing::span::Entered<'span>,
		}
	}
}

/// Requires a tracing::Subscriber to process span traces,
/// this is available when running with client (and relevant cli params)
pub struct TracingProxy {
	next_id: u64,
	spans: Vec<(u64, rent_span::SpanAndGuard)>,
}

impl Drop for TracingProxy {
	fn drop(&mut self) {
		while let Some((_, mut sg)) = self.spans.pop() {
			sg.rent_all_mut(|s| { s.span.record("tracing_proxy_ok", &false); });
		}
	}
}

impl TracingProxy {
	pub fn new() -> TracingProxy {
		let spans: Vec<(u64, rent_span::SpanAndGuard)> = Vec::new();
		TracingProxy {
			// Span ids start from 1 - we will use 0 as special case for unregistered spans
			next_id: 1,
			spans,
		}
	}
}

/// For spans to be recorded they must be registered in `span_dispatch`
impl TracingProxy {
	fn create_registered_span(&mut self, target: &str, name: &str) -> u64 {
		let create_span: Result<tracing::Span, String> = span_dispatch::create_registered_span(target, name);
		let id;
		match create_span {
			Ok(span) => {
				self.next_id += 1;
				id = self.next_id;
				let sg = rent_span::SpanAndGuard::new(
					Box::new(span),
					|span| span.enter(),
				);
				self.spans.push((id, sg));
			}
			Err(e) => {
				id = 0;
				log::info!("{}", e);
			}
		}
		let spans_len = self.spans.len();
		if spans_len > MAX_SPANS_LEN {
			// This is to prevent unbounded growth of Vec and could mean one of the following:
			// 1. Too many nested spans, or MAX_SPANS_LEN is too low.
			// 2. Not correctly exiting spans due to drop impl not running (panic in runtime)
			// 3. Not correctly exiting spans due to misconfiguration / misuse
			log::warn!("MAX_SPANS_LEN exceeded, removing oldest span, recording `sp_profiler_ok = false`");
			let mut sg = self.spans.remove(0).1;
			sg.rent_all_mut(|s| { s.span.record("tracing_proxy_ok", &false); });
		}
		id
	}

	fn exit_span(&mut self, id: u64) {
		if id == 0 { return; }
		match self.spans.pop() {
			Some(v) => {
				let mut last_span_id = v.0;
				while id < last_span_id {
					log::warn!("Span ids not equal! id parameter given: {}, last span: {}", id, last_span_id);
					if let Some(mut s) = self.spans.pop() {
						last_span_id = s.0;
						if id != last_span_id {
							s.1.rent_all_mut(|s| { s.span.record("tracing_proxy_ok", &false); });
						}
					} else {
						log::warn!("Span id not found {}", id);
						return;
					}
				}
			},
			None => {
				log::warn!("Span id: {} not found", id);
				return;
			}
		}
	}
}
