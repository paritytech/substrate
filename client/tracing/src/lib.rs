// Copyright 2019 Parity Technologies (UK) Ltd.
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
//! Monitor performance throughout the codebase via the creation of `Span`s.
//! A span is set in the following way:
//! ```
//! let span = tracing::span!(tracing::Level::INFO, "my_span_name");
//! let _enter = span.enter();
//! ```
//! To begin timing, a span must be entered. When the span is dropped, the execution time
//! is recorded and details sent to the `Receiver` which defines how to process it.
//!
//! Currently we provide `Log` (default) and `Telemetry` variants for `Receiver`

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use parking_lot::Mutex;
use tracing_core::{event::Event, Level, metadata::Metadata, span::{Attributes, Id, Record}, subscriber::Subscriber};

use substrate_telemetry::{telemetry, SUBSTRATE_INFO};
use grafana_data_source::{self, record_metrics};

/// Used to configure how to receive the metrics
#[derive(Debug, Clone)]
pub enum TracingReceiver {
	/// Output to logger
	Log,
	/// Output to telemetry
	Telemetry,
	/// Output to Grafana,
	Grafana,
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
	/// either with a level "paint=trace"
	/// or without "paint".
	pub fn new(receiver: TracingReceiver, targets: &String) -> Self {
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
	match s.find("=") {
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
		let span_datum = SpanDatum {
			id: id,
			name: attrs.metadata().name(),
			target: attrs.metadata().target(),
			level: attrs.metadata().level().clone(),
			line: attrs.metadata().line().unwrap_or(0),
			start_time: Instant::now(),
			overall_time: Duration::from_nanos(0),
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
			TracingReceiver::Grafana => send_grafana(span_datum),
		}
	}
}

fn print_log(span_datum: SpanDatum) {
	let message = format!(
		"Tracing: {} {}: {}, line: {}, time: {} ns",
		span_datum.level,
		span_datum.target,
		span_datum.name,
		span_datum.line,
		span_datum.overall_time.as_nanos()
	);
	log::info!(target: "substrate_tracing", "{}", message);
}

fn send_telemetry(span_datum: SpanDatum) {
	telemetry!(SUBSTRATE_INFO; "tracing.profiling";
		"name" => span_datum.name,
		"target" => span_datum.target,
		"line" => span_datum.line,
		"time" => span_datum.overall_time.as_nanos(),
	);
}

fn send_grafana(span_datum: SpanDatum) {
	let name = format!("{}::{}", span_datum.target, span_datum.name);
	record_metrics!(name => span_datum.overall_time.as_nanos());
}
