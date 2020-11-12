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

use crate::Telemetries;
use futures::channel::mpsc;
use libp2p::wasm_ext::ExtTransport;
use parking_lot::Mutex;
use std::collections::HashMap;
use std::convert::TryInto;
use std::sync::Arc;
use tracing::{Event, Subscriber};
use tracing_subscriber::{layer::Context, registry::LookupSpan, Layer};

pub const TELEMETRY_LOG_SPAN: &str = "telemetry-logger";

#[derive(Debug)]
pub struct TelemetryLayer(Senders);

impl TelemetryLayer {
	/// TODO
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
				let id = span.id().into_u64();
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
							eprintln!(
								//target: "telemetry",
								"###### sent message as {}: {}", id, json,
							);
							if let Err(err) = sender.try_send((
								message_verbosity
									.try_into()
									.expect("telemetry log message verbosity are u8; qed"),
								json.clone(),
							)) {
								// TODO logs dont work here
								log::warn!(
									target: "telemetry",
									"Ignored telemetry message because of error on channel: {:?}",
									err,
								);
							}
						}
						_ => panic!("missing fields in telemetry log: {:?}", event),
					}
				} else {
					// TODO logs dont work here
					log::trace!(target: "telemetry", "Telemetry not set");
				}
			}
		}
	}
}

#[derive(Debug)]
struct TelemetryAttrs {
	message_verbosity: Option<u64>,
	json: Option<String>,
	id: u64,
}

impl TelemetryAttrs {
	fn new(id: u64) -> Self {
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
			let mut message = format!(r#"{{"id":{},"#, (*self.0).id);
			message.push_str(&value[1..]);
			(*self.0).json = Some(message)
		}
	}
}

#[derive(Default, Debug, Clone)]
pub struct Senders(
	Arc<Mutex<HashMap<u64, std::panic::AssertUnwindSafe<mpsc::Sender<(u8, String)>>>>>,
);

impl Senders {
	/// TODO doc
	pub fn insert(&self, id: u64, sender: mpsc::Sender<(u8, String)>) {
		self.0
			.lock()
			.insert(id, std::panic::AssertUnwindSafe(sender));
	}
}
