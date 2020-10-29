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
use std::sync::{Arc, Mutex};
use tracing::Subscriber;
use tracing_subscriber::{registry::LookupSpan, Layer};

pub struct TelemetryLayer(Senders);

impl TelemetryLayer {
	pub fn new() -> Self {
		Self(Default::default())
	}

	pub fn senders(&self) -> Senders {
		self.0.clone()
	}
}

impl<S> Layer<S> for TelemetryLayer where S: Subscriber + for<'a> LookupSpan<'a> {}

#[derive(Default, Debug, Clone)]
pub struct Senders(Arc<Mutex<Vec<std::panic::AssertUnwindSafe<mpsc::Sender<(u8, String)>>>>>);
