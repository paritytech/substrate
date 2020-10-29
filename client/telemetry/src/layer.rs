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

use futures::{channel::mpsc, prelude::*};
use std::sync::{Arc};
use tracing::{Subscriber, Event, Id, span::Attributes};
use tracing_subscriber::{registry::LookupSpan, Layer, layer::Context};
use parking_lot::Mutex;
use std::collections::HashMap;
use std::convert::TryInto;

pub const TELEMETRY_LOG_SPAN: &str = "telemetry-logger";

pub struct TelemetryLayer(Senders);

impl TelemetryLayer {
	pub fn new() -> Self {
		Self(Default::default())
	}

	pub fn senders(&self) -> Senders {
		self.0.clone()
	}
}

impl<S> Layer<S> for TelemetryLayer where S: Subscriber + for<'a> LookupSpan<'a> {
	fn on_event(&self, event: &Event<'_>, ctx: Context<S>) {
		for span in ctx.scope() {
			if span.name() == TELEMETRY_LOG_SPAN {
				let mut attrs = (None, None);
				let mut vis = TelemetryAttrsVisitor(&mut attrs);
				event.record(&mut vis);

				match attrs {
					(Some(message_verbosity), Some(json)) => {
						let id = span.id().into_u64();
						self.0.0.lock().get_mut(&id)
							.expect("a telemetry span has not been registered to the TelemetryLayer")
							.send((
								message_verbosity
									.try_into()
									.expect("telemetry log message verbosity are u8; qed"),
								json,
							));
					},
					_ => panic!("missing fields in telemetry log"),
				}
			}
		}
	}
}

struct TelemetryAttrsVisitor<'a>(&'a mut (Option<u64>, Option<String>));

impl<'a> tracing::field::Visit for TelemetryAttrsVisitor<'a> {
	fn record_debug(&mut self, field: &tracing::field::Field, value: &dyn std::fmt::Debug) {
		// noop
	}

	fn record_u64(&mut self, field: &tracing::field::Field, value: u64) {
		if field.name() == "message_verbosity" {
			(*self.0).0 = Some(value)
		}
	}

	fn record_str(&mut self, field: &tracing::field::Field, value: &str) {
		if field.name() == "json" {
			(*self.0).1 = Some(value.to_string())
		}
	}
}

#[derive(Default, Debug, Clone)]
pub struct Senders(Arc<Mutex<HashMap<u64, std::panic::AssertUnwindSafe<mpsc::Sender<(u8, String)>>>>>);

impl Senders {
	pub fn insert(&mut self, id: u64, sender: mpsc::Sender<(u8, String)>) {
		self.0.lock().insert(id, std::panic::AssertUnwindSafe(sender));
	}
}
