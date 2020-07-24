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

//! Instrumentation implementation for substrate.
//!
//! This crate is unstable and the API and usage may change.
//!
//! # Usage
//!
//! See `sp-tracing` for examples on how to use tracing.
//!
//! Currently we provide `Log` (default), `Telemetry` variants for `Receiver`

use rustc_hash::FxHashMap;
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use parking_lot::Mutex;
use serde::ser::{Serialize, Serializer, SerializeMap};
use tracing_core::{
	event::Event,
	field::{Visit, Field},
	Level,
	metadata::Metadata,
	span::{Attributes, Id, Record},
	subscriber::Subscriber,
};

use sc_telemetry::{telemetry, SUBSTRATE_INFO};
use sp_tracing::proxy::{WASM_NAME_KEY, WASM_TARGET_KEY, WASM_TRACE_IDENTIFIER};

const ZERO_DURATION: Duration = Duration::from_nanos(0);
const PROXY_TARGET: &'static str = "sp_tracing::proxy";

/// Used to configure how to receive the metrics
#[derive(Debug, Clone)]
pub enum TracingReceiver {
	/// Output to logger
	Log,
	/// Output to telemetry
	Telemetry,
}

impl Default for TracingReceiver {
	fn default() -> Self {
		Self::Log
	}
}

/// A handler for tracing `SpanDatum`
pub trait TraceHandler: Send + Sync {
	/// Process a `SpanDatum`
	fn handle_span(&self, span: SpanDatum);
}

/// Represents a single instance of a tracing span
#[derive(Debug)]
pub struct SpanDatum {
	/// id for this span
	pub id: u64,
	/// Name of the span
	pub name: String,
	/// Target, typically module
	pub target: String,
	/// Tracing Level - ERROR, WARN, INFO, DEBUG or TRACE
	pub level: Level,
	/// Line number in source
	pub line: u32,
	/// Time that the span was last entered
	pub start_time: Instant,
	/// Total duration of span while entered
	pub overall_time: Duration,
	/// Values recorded to this span
	pub values: Values,
}

/// Holds associated values for a tracing span
#[derive(Default, Clone, Debug)]
pub struct Values {
	/// HashMap of `bool` values
	pub bool_values: FxHashMap<String, bool>,
	/// HashMap of `i64` values
	pub i64_values: FxHashMap<String, i64>,
	/// HashMap of `u64` values
	pub u64_values: FxHashMap<String, u64>,
	/// HashMap of `String` values
	pub string_values: FxHashMap<String, String>,
}

impl Values {
	/// Returns a new instance of Values
	pub fn new() -> Self {
		Default::default()
	}

	/// Checks if all individual collections are empty
	pub fn is_empty(&self) -> bool {
		self.bool_values.is_empty() &&
			self.i64_values.is_empty() &&
			self.u64_values.is_empty() &&
			self.string_values.is_empty()
	}
}

impl Visit for Values {
	fn record_i64(&mut self, field: &Field, value: i64) {
		self.i64_values.insert(field.name().to_string(), value);
	}

	fn record_u64(&mut self, field: &Field, value: u64) {
		self.u64_values.insert(field.name().to_string(), value);
	}

	fn record_bool(&mut self, field: &Field, value: bool) {
		self.bool_values.insert(field.name().to_string(), value);
	}

	fn record_str(&mut self, field: &Field, value: &str) {
		self.string_values.insert(field.name().to_string(), value.to_owned());
	}

	fn record_debug(&mut self, field: &Field, value: &dyn std::fmt::Debug) {
		self.string_values.insert(field.name().to_string(), format!("{:?}", value).to_owned());
	}
}

impl Serialize for Values {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
		where S: Serializer,
	{
		let len = self.bool_values.len() + self.i64_values.len() + self.u64_values.len() + self.string_values.len();
		let mut map = serializer.serialize_map(Some(len))?;
		for (k, v) in &self.bool_values {
			map.serialize_entry(k, v)?;
		}
		for (k, v) in &self.i64_values {
			map.serialize_entry(k, v)?;
		}
		for (k, v) in &self.u64_values {
			map.serialize_entry(k, v)?;
		}
		for (k, v) in &self.string_values {
			map.serialize_entry(k, v)?;
		}
		map.end()
	}
}

impl fmt::Display for Values {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let bool_iter = self.bool_values.iter().map(|(k, v)| format!("{}={}", k, v));
		let i64_iter = self.i64_values.iter().map(|(k, v)| format!("{}={}", k, v));
		let u64_iter = self.u64_values.iter().map(|(k, v)| format!("{}={}", k, v));
		let string_iter = self.string_values.iter().map(|(k, v)| format!("{}=\"{}\"", k, v));
		let values = bool_iter.chain(i64_iter).chain(u64_iter).chain(string_iter).collect::<Vec<String>>().join(", ");
		write!(f, "{}", values)
	}
}

impl slog::SerdeValue for Values {
	fn as_serde(&self) -> &dyn erased_serde::Serialize {
		self
	}

	fn to_sendable(&self) -> Box<dyn slog::SerdeValue + Send + 'static> {
		Box::new(self.clone())
	}
}

impl slog::Value for Values {
	fn serialize(
		&self,
		_record: &slog::Record,
		key: slog::Key,
		ser: &mut dyn slog::Serializer,
	) -> slog::Result {
		ser.emit_serde(key, self)
	}
}

/// Responsible for assigning ids to new spans, which are not re-used.
pub struct ProfilingSubscriber {
	next_id: AtomicU64,
	targets: Vec<(String, Level)>,
	trace_handler: Box<dyn TraceHandler>,
	span_data: Mutex<FxHashMap<u64, SpanDatum>>,
}

impl ProfilingSubscriber {
	/// Takes a `TracingReceiver` and a comma separated list of targets,
	/// either with a level: "pallet=trace,frame=debug"
	/// or without: "pallet,frame" in which case the level defaults to `trace`.
	/// wasm_tracing indicates whether to enable wasm traces
	pub fn new(receiver: TracingReceiver, targets: &str) -> ProfilingSubscriber {
		match receiver {
			TracingReceiver::Log => Self::new_with_handler(Box::new(LogTraceHandler), targets),
			TracingReceiver::Telemetry => Self::new_with_handler(
				Box::new(TelemetryTraceHandler),
				targets,
			),
		}
	}

	/// Allows use of a custom TraceHandler to create a new instance of ProfilingSubscriber.
	/// Takes a comma separated list of targets,
	/// either with a level, eg: "pallet=trace"
	/// or without: "pallet" in which case the level defaults to `trace`.
	/// wasm_tracing indicates whether to enable wasm traces
	pub fn new_with_handler(trace_handler: Box<dyn TraceHandler>, targets: &str)
		-> ProfilingSubscriber
	{
		let targets: Vec<_> = targets.split(',').map(|s| parse_target(s)).collect();
		ProfilingSubscriber {
			next_id: AtomicU64::new(1),
			targets,
			trace_handler,
			span_data: Mutex::new(FxHashMap::default()),
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

// Default to TRACE if no level given or unable to parse Level
// We do not support a global `Level` currently
fn parse_target(s: &str) -> (String, Level) {
	match s.find('=') {
		Some(i) => {
			let target = s[0..i].to_string();
			if s.len() > i {
				let level = s[i + 1..s.len()].parse::<Level>().unwrap_or(Level::TRACE);
				(target, level)
			} else {
				(target, Level::TRACE)
			}
		}
		None => (s.to_string(), Level::TRACE)
	}
}

impl Subscriber for ProfilingSubscriber {
	fn enabled(&self, metadata: &Metadata<'_>) -> bool {
		if metadata.target() == PROXY_TARGET || self.check_target(metadata.target(), metadata.level()) {
			log::debug!(target: "tracing", "Enabled target: {}, level: {}", metadata.target(), metadata.level());
			true
		} else {
			log::debug!(target: "tracing", "Disabled target: {}, level: {}", metadata.target(), metadata.level());
			false
		}
	}

	fn new_span(&self, attrs: &Attributes<'_>) -> Id {
		let id = self.next_id.fetch_add(1, Ordering::Relaxed);
		let mut values = Values::default();
		attrs.record(&mut values);
		// If this is a wasm trace, check if target/level is enabled
		if let Some(wasm_target) = values.string_values.get(WASM_TARGET_KEY) {
			if !self.check_target(wasm_target, attrs.metadata().level()) {
				return Id::from_u64(id);
			}
		}
		let span_datum = SpanDatum {
			id,
			name: attrs.metadata().name().to_owned(),
			target: attrs.metadata().target().to_owned(),
			level: attrs.metadata().level().clone(),
			line: attrs.metadata().line().unwrap_or(0),
			start_time: Instant::now(),
			overall_time: ZERO_DURATION,
			values,
		};
		self.span_data.lock().insert(id, span_datum);
		Id::from_u64(id)
	}

	fn record(&self, span: &Id, values: &Record<'_>) {
		let mut span_data = self.span_data.lock();
		if let Some(s) = span_data.get_mut(&span.into_u64()) {
			values.record(&mut s.values);
		}
	}

	fn record_follows_from(&self, _span: &Id, _follows: &Id) {}

	fn event(&self, _event: &Event<'_>) {}

	fn enter(&self, span: &Id) {
		let mut span_data = self.span_data.lock();
		let start_time = Instant::now();
		if let Some(mut s) = span_data.get_mut(&span.into_u64()) {
			s.start_time = start_time;
		}
	}

	fn exit(&self, span: &Id) {
		let end_time = Instant::now();
		let mut span_data = self.span_data.lock();
		if let Some(mut s) = span_data.get_mut(&span.into_u64()) {
			s.overall_time = end_time - s.start_time + s.overall_time;
		}
	}

	fn try_close(&self, span: Id) -> bool {
		let span_datum = {
			let mut span_data = self.span_data.lock();
			span_data.remove(&span.into_u64())
		};
		if let Some(mut span_datum) = span_datum {
			if span_datum.name == WASM_TRACE_IDENTIFIER {
				span_datum.values.bool_values.insert("wasm".to_owned(), true);
				if let Some(n) = span_datum.values.string_values.remove(WASM_NAME_KEY) {
					span_datum.name = n;
				}
				if let Some(t) = span_datum.values.string_values.remove(WASM_TARGET_KEY) {
					span_datum.target = t;
				}
			}
			if self.check_target(&span_datum.target, &span_datum.level) {
				self.trace_handler.handle_span(span_datum);
			}
		};
		true
	}
}

/// TraceHandler for sending span data to the logger
pub struct LogTraceHandler;

fn log_level(level: Level) -> log::Level {
	match level {
		Level::TRACE => log::Level::Trace,
		Level::DEBUG => log::Level::Debug,
		Level::INFO => log::Level::Info,
		Level::WARN => log::Level::Warn,
		Level::ERROR => log::Level::Error,
	}
}

impl TraceHandler for LogTraceHandler {
	fn handle_span(&self, span_datum: SpanDatum) {
		if span_datum.values.is_empty() {
			log::log!(
				log_level(span_datum.level), 
				"{}: {}, time: {}",
				span_datum.target,
				span_datum.name,
				span_datum.overall_time.as_nanos(),
			);
		} else {
			log::log!(
				log_level(span_datum.level),
				"{}: {}, time: {}, {}",
				span_datum.target,
				span_datum.name,
				span_datum.overall_time.as_nanos(),
				span_datum.values,
			);
		}
	}
}

/// TraceHandler for sending span data to telemetry,
/// Please see telemetry documentation for details on how to specify endpoints and
/// set the required telemetry level to activate tracing messages
pub struct TelemetryTraceHandler;

impl TraceHandler for TelemetryTraceHandler {
	fn handle_span(&self, span_datum: SpanDatum) {
		telemetry!(SUBSTRATE_INFO; "tracing.profiling";
			"name" => span_datum.name,
			"target" => span_datum.target,
			"line" => span_datum.line,
			"time" => span_datum.overall_time.as_nanos(),
			"values" => span_datum.values
		);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::sync::Arc;

	struct TestTraceHandler {
		spans: Arc<Mutex<Vec<SpanDatum>>>,
	}

	impl TraceHandler for TestTraceHandler {
		fn handle_span(&self, sd: SpanDatum) {
			self.spans.lock().push(sd);
		}
	}

	fn setup_subscriber() -> (ProfilingSubscriber, Arc<Mutex<Vec<SpanDatum>>>) {
		let spans = Arc::new(Mutex::new(Vec::new()));
		let handler = TestTraceHandler {
			spans: spans.clone(),
		};
		let test_subscriber = ProfilingSubscriber::new_with_handler(
			Box::new(handler),
			"test_target"
		);
		(test_subscriber, spans)
	}

	#[test]
	fn test_span() {
		let (sub, spans) = setup_subscriber();
		let _sub_guard = tracing::subscriber::set_default(sub);
		let span = tracing::info_span!(target: "test_target", "test_span1");
		assert_eq!(spans.lock().len(), 0);
		let _guard = span.enter();
		assert_eq!(spans.lock().len(), 0);
		drop(_guard);
		drop(span);
		assert_eq!(spans.lock().len(), 1);
		let sd = spans.lock().remove(0);
		assert_eq!(sd.name, "test_span1");
		assert_eq!(sd.target, "test_target");
		let time: u128 = sd.overall_time.as_nanos();
		assert!(time > 0);
	}

	#[test]
	fn test_span_values() {
		let (sub, spans) = setup_subscriber();
		let _sub_guard = tracing::subscriber::set_default(sub);
		let test_bool = true;
		let test_u64 = 1u64;
		let test_i64 = 2i64;
		let test_str = "test_str";
		let span = tracing::info_span!(
			target: "test_target",
			"test_span1",
			test_bool,
			test_u64,
			test_i64,
			test_str
		);
		let _guard = span.enter();
		drop(_guard);
		drop(span);
		let sd = spans.lock().remove(0);
		assert_eq!(sd.name, "test_span1");
		assert_eq!(sd.target, "test_target");
		let values = sd.values;
		assert_eq!(values.bool_values.get("test_bool").unwrap(), &test_bool);
		assert_eq!(values.u64_values.get("test_u64").unwrap(), &test_u64);
		assert_eq!(values.i64_values.get("test_i64").unwrap(), &test_i64);
		assert_eq!(values.string_values.get("test_str").unwrap(), &test_str.to_owned());
	}
}
