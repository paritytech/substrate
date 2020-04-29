use std::sync::Arc;
use parking_lot::Mutex;
use std::collections::BTreeMap;
use rental;
use lazy_static;
use rustc_hash::FxHashMap;

use crate::span_dispatch;

const MAX_SPANS_LEN: usize = 1000;

lazy_static! {
	static ref PROXY: Arc<Mutex<TracingProxy>> = Arc::new(Mutex::new(TracingProxy::new()));
}

pub fn create_registered_span(target: &str, name: &str) -> u64 {
	PROXY.lock().create_registered_span(target, name)
}

pub fn exit_span(id: u64) {
	PROXY.lock().exit_span(id);
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
	spans: FxHashMap<u64, rent_span::SpanAndGuard>,
}

impl TracingProxy {
	pub fn new() -> TracingProxy {
		let spans: FxHashMap<u64, rent_span::SpanAndGuard> = FxHashMap::default();
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
				self.spans.insert(id, sg);
			}
			Err(e) => {
				id = 0;
				log::info!("{}", e);
			}
		}
		let spans_len = self.spans.len();
		if spans_len > MAX_SPANS_LEN {
			log::warn!("MAX_SPANS_LEN exceeded, removing oldest span, recording `sp_profiler_ok = false`");
			let mut all_keys: Vec<_> = self.spans.keys().cloned().collect();
			all_keys.sort();
			let key = all_keys.iter().next().expect("Just got the key, so must be able to get first item.");
			let mut sg = self.spans.remove(&key).expect("Just got the key so must be in the map");
			sg.rent_all_mut(|s| { s.span.record("tracing_proxy_ok", &false); });
		}
		id
	}

	fn exit_span(&mut self, id: u64) {
		if id == 0 { return; }
		match self.spans.remove(&id) {
			Some(_) => (),
			None => {
				log::warn!("Span id: {} not found", id);
				return;
			}
		}
	}

//	fn record_info(&mut self, id: u64, info: &str) {
//		if let Some(mut sg) = self.spans.get_mut(&id) {
//			sg.rent_all_mut(|s| { s.span.record("info", &info); });
//		}
//	}
}
