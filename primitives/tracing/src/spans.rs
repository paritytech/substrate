// // Copyright 2019-2020 Parity Technologies (UK) Ltd.
// // This file is part of Substrate.
//
// // Substrate is free software: you can redistribute it and/or modify
// // it under the terms of the GNU General Public License as published by
// // the Free Software Foundation, either version 3 of the License, or
// // (at your option) any later version.
//
// // Substrate is distributed in the hope that it will be useful,
// // but WITHOUT ANY WARRANTY; without even the implied warranty of
// // MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// // GNU General Public License for more details.
//
// // You should have received a copy of the GNU General Public License
// // along with Substrate.  If not, see <http://www.gnu.org/licenses/>.
//
// //! Instrumentation implementation for substrate.
// //!
// //! This crate is unstable and the API and usage may change.
// //!
// //! # Usage
// //!
// //! See `sp-tracing` for examples on how to use tracing.
// //!
// //! Currently we provide `Log` (default), `Telemetry` variants for `Receiver`
//
// use rustc_hash::FxHashMap;
// use std::fmt;
// use std::sync::Arc;
// use std::sync::atomic::{AtomicU64, Ordering};
// use std::time::{Duration, Instant};
//
// use parking_lot::Mutex;
// use serde::ser::{Serialize, Serializer, SerializeMap};
// use slog::{SerdeValue, Value};
// use tracing::{
// 	event::Event,
// 	field::{Visit, Field},
// 	Level,
// 	metadata::Metadata,
// 	span::{Attributes, Id, Record},
// 	subscriber::Subscriber,
// };
// use tracing_subscriber::CurrentSpan;
//
// pub static SPAN_STORE: Arc<Mutex<FxHashMap<u64, SpanDatum>>> = Arc::new(Mutex::new(FxHashMap::default()));
// pub static NEXT_ID: AtomicU64 = AtomicU64::new(1);
// pub static CURRENT_SPAN: CurrentSpan = CurrentSpan::new();
//
// // Used to ensure we don't accumulate too many proxied spans,
// // or associated events
// const LEN_LIMIT: usize = 128;
//
// /// Create and enter a `tracing` Span, returning the span id,
// /// which should be passed to `exit_span(id)` to signal that the span should exit.
// // fn parameter identifiers should match the const values above
// pub fn enter_span(target: &str, name: &str) -> u64 {
// 	let id = next_id();
// 	let span_datum = SpanDatum {
// 		id,
// 		parent_id: CURRENT_SPAN.id().map(|p| p.into_u64()),
// 		name: name.to_owned(),
// 		target: target.to_owned(),
// 		level: Level::INFO,
// 		line: 0,
// 		start_time: Instant::now(),
// 		overall_time: Default::default(),
// 		values: Visitor(FxHashMap::default()),
// 		events: vec![],
// 	};
// 	CURRENT_SPAN.enter(Id::from_u64(span_datum.id));
// 	SPAN_STORE.lock().insert(id, span_datum);
// 	id
// }
//
// /// Exit a span by dropping it along with it's associated guard.
// // fn parameter identifier should match the const value above
// pub fn exit_span(id: u64) {
//
// }
//
// /// Represents a single instance of a tracing span, complete with values
// /// and direct child events
// #[derive(Debug)]
// pub struct SpanDatum {
// 	pub id: u64,
// 	pub parent_id: Option<u64>,
// 	pub name: String,
// 	pub target: String,
// 	pub level: Level,
// 	pub line: u32,
// 	pub start_time: Instant,
// 	pub overall_time: Duration,
// 	pub values: Visitor,
// 	pub events: Vec<TraceEvent>,
// }
//
// /// Represents a tracing event, complete with values
// #[derive(Debug)]
// pub struct TraceEvent {
// 	pub name: &'static str,
// 	pub target: String,
// 	pub level: Level,
// 	pub visitor: Visitor,
// 	pub parent_id: Option<u64>,
// }
//
// /// Universal id source for tracing spans
// pub fn next_id() -> u64 {
// 	NEXT_ID.fetch_add(1, Ordering::Relaxed)
// }
//
// ///
// pub fn span_store() -> Arc<Mutex<FxHashMap<u64, SpanDatum>>> {
// 	SPAN_STORE.clone()
// }
//
// /// Holds associated values for a tracing span
// #[derive(Clone, Debug)]
// pub struct Visitor(FxHashMap<String, String>);
//
// impl Visitor {
// 	/// Consume the Visitor, returning the inner FxHashMap
// 	pub fn into_inner(self) -> FxHashMap<String, String> {
// 		self.0
// 	}
// }
//
// impl Visit for Visitor {
// 	fn record_i64(&mut self, field: &Field, value: i64) {
// 		self.0.insert(field.name().to_string(), value.to_string());
// 	}
//
// 	fn record_u64(&mut self, field: &Field, value: u64) {
// 		self.0.insert(field.name().to_string(), value.to_string());
// 	}
//
// 	fn record_bool(&mut self, field: &Field, value: bool) {
// 		self.0.insert(field.name().to_string(), value.to_string());
// 	}
//
// 	fn record_str(&mut self, field: &Field, value: &str) {
// 		self.0.insert(field.name().to_string(), value.to_owned());
// 	}
//
// 	fn record_debug(&mut self, field: &Field, value: &dyn std::fmt::Debug) {
// 		self.0.insert(field.name().to_string(), format!("{:?}", value));
// 	}
// }
//
// impl Serialize for Visitor {
// 	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
// 		where S: Serializer,
// 	{
// 		let mut map = serializer.serialize_map(Some(self.0.len()))?;
// 		for (k, v) in &self.0 {
// 			map.serialize_entry(k, v)?;
// 		}
// 		map.end()
// 	}
// }
//
// impl fmt::Display for Visitor {
// 	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
// 		let values = self.0.iter().map(|(k, v)| format!("{}={}", k, v)).collect::<Vec<String>>().join(", ");
// 		write!(f, "{}", values)
// 	}
// }
//
// impl SerdeValue for Visitor {
// 	fn as_serde(&self) -> &dyn erased_serde::Serialize {
// 		self
// 	}
//
// 	fn to_sendable(&self) -> Box<dyn SerdeValue + Send + 'static> {
// 		Box::new(self.clone())
// 	}
// }
//
// impl Value for Visitor {
// 	fn serialize(
// 		&self,
// 		_record: &slog::Record,
// 		key: slog::Key,
// 		ser: &mut dyn slog::Serializer,
// 	) -> slog::Result {
// 		ser.emit_serde(key, self)
// 	}
// }
