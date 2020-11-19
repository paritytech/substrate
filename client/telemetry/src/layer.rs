// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use futures::channel::mpsc;
use parking_lot::Mutex;
use std::collections::HashMap;
use std::convert::TryInto;
use std::sync::Arc;
use tracing::{Event, Id, Subscriber};
use tracing_subscriber::{layer::Context, registry::LookupSpan, Layer};

/// Span name used to report the telemetry.
pub const TELEMETRY_LOG_SPAN: &str = "telemetry-logger";

/// `Layer` that handles the logs for telemetries.
#[derive(Debug)]
pub struct TelemetryLayer(Senders);

impl TelemetryLayer {
	/// Create a new [`TelemetryLayer`] using the [`Senders`] provided in argument.
	pub fn new(senders: Senders) -> Self {
		Self(senders)
	}
}

impl<S> Layer<S> for TelemetryLayer
where
	S: Subscriber + for<'a> LookupSpan<'a>,
{
	fn on_event(&self, event: &Event<'_>, ctx: Context<S>) {
		if event.metadata().target() != TELEMETRY_LOG_SPAN {
			return;
		}

		if let Some(span) = ctx.lookup_current() {
			let parents = span.parents();

			if let Some(span) = std::iter::once(span)
				.chain(parents)
				.find(|x| x.name() == TELEMETRY_LOG_SPAN)
			{
				let id = span.id();
				if let Some(sender) = (self.0).0.lock().get_mut(&id) {
					let mut attrs = TelemetryAttrs::new(id);
					let mut vis = TelemetryAttrsVisitor(&mut attrs);
					event.record(&mut vis);

					match attrs {
						TelemetryAttrs {
							message_verbosity: Some(message_verbosity),
							json: Some(json),
							..
						} => {
							let _ = sender.try_send((
								message_verbosity
									.try_into()
									.expect("telemetry log message verbosity are u8; qed"),
								json,
							));
						}
						_ => panic!("missing fields in telemetry log: {:?}", event),
					}
				}
			}
		}
	}
}

#[derive(Debug)]
struct TelemetryAttrs {
	message_verbosity: Option<u64>,
	json: Option<String>,
	id: Id,
}

impl TelemetryAttrs {
	fn new(id: Id) -> Self {
		Self {
			message_verbosity: None,
			json: None,
			id,
		}
	}
}

#[derive(Debug)]
struct TelemetryAttrsVisitor<'a>(&'a mut TelemetryAttrs);

impl<'a> tracing::field::Visit for TelemetryAttrsVisitor<'a> {
	fn record_debug(&mut self, _field: &tracing::field::Field, _value: &dyn std::fmt::Debug) {
		// noop
	}

	fn record_u64(&mut self, field: &tracing::field::Field, value: u64) {
		if field.name() == "message_verbosity" {
			(*self.0).message_verbosity = Some(value)
		}
	}

	fn record_str(&mut self, field: &tracing::field::Field, value: &str) {
		if field.name() == "json" {
			// NOTE: this is a hack to inject the span id into the json
			let mut message = format!(r#"{{"id":{},"#, (*self.0).id.into_u64());
			message.push_str(&value[1..]);
			(*self.0).json = Some(message)
		}
	}
}

/// A collection of `futures::channel::mpsc::Sender` with their associated span's ID.
///
/// This is used by [`TelemetryLayer`] to route the log events to the correct channel based on the
/// span's ID.
#[derive(Default, Debug, Clone)]
pub struct Senders(
	Arc<Mutex<HashMap<Id, std::panic::AssertUnwindSafe<mpsc::Sender<(u8, String)>>>>>,
);

impl Senders {
	/// Insert a channel `Sender` to the collection using an id (`u64`) for its key.
	pub fn insert(&self, id: Id, sender: mpsc::Sender<(u8, String)>) {
		self.0
			.lock()
			.insert(id, std::panic::AssertUnwindSafe(sender));
	}
}
