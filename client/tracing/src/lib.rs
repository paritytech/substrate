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

use std::collections::HashMap;
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use parking_lot::Mutex;
use serde::ser::{Serialize, Serializer, SerializeMap};
use slog::{SerdeValue, Value};
use tracing_core::{
	event::Event,
	field::{Visit, Field},
	Level,
	metadata::Metadata,
	span::{Attributes, Id, Record},
	subscriber::Subscriber
};

use sc_telemetry::{telemetry, SUBSTRATE_INFO};

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

#[derive(Debug)]
struct SpanDatum {
	id: u64,
	name: &'static str,
	target: &'static str,
	level: Level,
	line: u32,
	start_time: Instant,
	overall_time: Duration,
	values: Visitor,
}

#[derive(Clone, Debug)]
struct Visitor(Vec<(String, String)>);

impl Visit for Visitor {
	fn record_i64(&mut self, field: &Field, value: i64) {
		self.record_debug(field, &value)
	}

	fn record_u64(&mut self, field: &Field, value: u64) {
		self.record_debug(field, &value)
	}

	fn record_bool(&mut self, field: &Field, value: bool) {
		self.record_debug(field, &value)
	}

	fn record_debug(&mut self, field: &Field, value: &dyn std::fmt::Debug) {
		self.0.push((field.name().to_string(), format!("{:?}",value)));
	}
}

impl Serialize for Visitor {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
		where S: Serializer,
	{
		let mut map = serializer.serialize_map(Some(self.0.len()))?;
		for (k, v) in &self.0 {
			map.serialize_entry(k, v)?;
		}
		map.end()
	}
}

impl fmt::Display for Visitor {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let values = self.0.iter().map(|(k,v)| format!("{}={}",k,v)).collect::<Vec<String>>().join(", ");
		write!(f, "{}", values)
	}
}

impl SerdeValue for Visitor {
	fn as_serde(&self) -> &dyn erased_serde::Serialize {
		self
	}

	fn to_sendable(&self) -> Box<dyn SerdeValue + Send + 'static> {
		Box::new(self.clone())
	}
}

impl Value for Visitor {
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
	receiver: TracingReceiver,
	span_data: Mutex<HashMap<u64, SpanDatum>>,
}

impl ProfilingSubscriber {
	/// Takes a `Receiver` and a comma separated list of targets,
	/// either with a level: "pallet=trace"
	/// or without: "pallet".
	pub fn new(receiver: TracingReceiver, targets: &str) -> Self {
		let targets: Vec<_> = targets.split(',').map(|s| parse_target(s)).collect();
		ProfilingSubscriber {
			next_id: AtomicU64::new(1),
			targets,
			receiver,
			span_data: Mutex::new(HashMap::new()),
		}
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
		for t in &self.targets {
			if metadata.target().starts_with(t.0.as_str()) && metadata.level() <= &t.1 {
				log::debug!("Enabled target: {}, level: {}", metadata.target(), metadata.level());
				return true;
			} else {
				log::debug!("Disabled target: {}, level: {}", metadata.target(), metadata.level());
			}
		}
		false
	}

	fn new_span(&self, attrs: &Attributes<'_>) -> Id {
		let id = self.next_id.fetch_add(1, Ordering::Relaxed);
		let mut values = Visitor(Vec::new());
		attrs.record(&mut values);
		let span_datum = SpanDatum {
			id,
			name: attrs.metadata().name(),
			target: attrs.metadata().target(),
			level: attrs.metadata().level().clone(),
			line: attrs.metadata().line().unwrap_or(0),
			start_time: Instant::now(),
			overall_time: Duration::from_nanos(0),
			values,
		};
		self.span_data.lock().insert(id, span_datum);
		Id::from_u64(id)
	}

	fn record(&self, _span: &Id, _values: &Record<'_>) {}

	fn record_follows_from(&self, _span: &Id, _follows: &Id) {}

	fn event(&self, _event: &Event<'_>) {}

	fn enter(&self, span: &Id) {
		let mut span_data = self.span_data.lock();
		let start_time = Instant::now();
		if let Some(mut s) = span_data.get_mut(&span.into_u64()) {
			s.start_time = start_time;
		} else {
			log::warn!("Tried to enter span {:?} that has already been closed!", span);
		}
	}

	fn exit(&self, span: &Id) {
		let mut span_data = self.span_data.lock();
		let end_time = Instant::now();
		if let Some(mut s) = span_data.get_mut(&span.into_u64()) {
			s.overall_time = end_time - s.start_time + s.overall_time;
		}
	}

	fn try_close(&self, span: Id) -> bool {
		let mut span_data = self.span_data.lock();
		if let Some(data) = span_data.remove(&span.into_u64()) {
			self.send_span(data);
		};
		true
	}
}

impl ProfilingSubscriber {
	fn send_span(&self, span_datum: SpanDatum) {
		match self.receiver {
			TracingReceiver::Log => print_log(span_datum),
			TracingReceiver::Telemetry => send_telemetry(span_datum),
		}
	}
}

fn print_log(span_datum: SpanDatum) {
	if span_datum.values.0.is_empty() {
		log::info!("TRACING: {} {}: {}, line: {}, time: {}",
			span_datum.level,
			span_datum.target,
			span_datum.name,
			span_datum.line,
			span_datum.overall_time.as_nanos(),
		);
	} else {
		log::info!("TRACING: {} {}: {}, line: {}, time: {}, {}",
			span_datum.level,
			span_datum.target,
			span_datum.name,
			span_datum.line,
			span_datum.overall_time.as_nanos(),
			span_datum.values
		);
	}
}

fn send_telemetry(span_datum: SpanDatum) {
	telemetry!(SUBSTRATE_INFO; "tracing.profiling";
		"name" => span_datum.name,
		"target" => span_datum.target,
		"line" => span_datum.line,
		"time" => span_datum.overall_time.as_nanos(),
		"values" => span_datum.values
	);
}

