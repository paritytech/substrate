// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
//!	let _enter = span.enter();
//! ```
//! To begin timing, a span must be entered. When the span is dropped, the execution time
//! is recorded and details sent to the `Receiver` which defines how to process it.
//!
//! Currently we provide a single `Telemetry` variant for `Receiver`

use std::sync::atomic::{AtomicU64, Ordering};

use parking_lot::Mutex;
use tracing_core::{event::Event, Level, metadata::Metadata, span::{Attributes, Id, Record}, subscriber::Subscriber};

use substrate_telemetry::{telemetry, SUBSTRATE_INFO};

/// Used to configure how to receive the metrics
pub enum Receiver {
	Telemetry,
}

#[derive(Debug, Default)]
struct SpanDatum {
	id: u64,
	name: &'static str,
	target: String,
	line: u32,
	start_time: u64,
	overall_time: u64,
}

/// Responsible for assigning ids to new spans, which are not re-used.
pub struct ProfilingSubscriber {
	next_id: AtomicU64,
	clock: quanta::Clock,
	targets: Vec<(String, Level)>,
	receiver: Receiver,
	span_data: Mutex<Vec<SpanDatum>>,
}

impl ProfilingSubscriber {
	/// Takes a `Receiver` and a comma separated list of targets,
	/// either with a level "paint=trace"
	/// or without "paint".
	pub fn new(receiver: Receiver, targets: &String) -> Self {
		let targets: Vec<_> = targets.split(',').map(|s| parse_target(s)).collect();
		ProfilingSubscriber {
			next_id: AtomicU64::new(1),
			clock: quanta::Clock::new(),
			targets,
			receiver,
			span_data: Mutex::new(Vec::new()),
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
			id: id as u64,
			name: attrs.metadata().name(),
			target: attrs.metadata().target().to_string(),
			line: attrs.metadata().line().unwrap_or(0),
			..Default::default()
		};
		self.span_data.lock().push(span_datum);
		Id::from_u64(id)
	}

	fn record(&self, _span: &Id, _values: &Record<'_>) {}

	fn record_follows_from(&self, _span: &Id, _follows: &Id) {}

	fn event(&self, _event: &Event<'_>) {}

	fn enter(&self, span: &Id) {
		let start_time = self.clock.now();
		let mut sd = self.span_data.lock();
		if let Ok(idx) = sd.binary_search_by_key(&span.into_u64(), |s| s.id) {
			sd[idx].start_time = start_time;
		} else {
			log::warn!("Tried to enter span {:?} that has already been closed!", span);
		}
	}

	fn exit(&self, span: &Id) {
		let end_time = self.clock.now();
		{
			let mut sd = self.span_data.lock();
			if let Ok(idx) = sd.binary_search_by_key(&span.into_u64(), |s| s.id) {
				sd[idx].overall_time = end_time - sd[idx].start_time + sd[idx].overall_time;
			} else { return; }
		}
	}

	fn try_close(&self, span: Id) -> bool {
		let mut sd = self.span_data.lock();
		if let Ok(idx) = sd.binary_search_by_key(&span.into_u64(), |s| s.id) {
			self.send_span(sd.remove(idx));
		}
		true
	}
}

impl ProfilingSubscriber {
	fn send_span(&self, span_datum: SpanDatum) {
		match self.receiver {
			Receiver::Telemetry => send_telemetry(span_datum),
		}
	}
}

fn send_telemetry(span_datum: SpanDatum) {
	telemetry!(SUBSTRATE_INFO; "instrumentation.profiling";
		"name" => span_datum.name,
		"target" => span_datum.target,
		"line" => span_datum.line,
		"time" => span_datum.overall_time,
	);
}