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

//! Logger wrapper around `tracing::Subscriber`.

use std::sync::Arc;

#[derive(Clone)]
pub enum Logger {
	Sink,
	Logger(Arc<dyn tracing::Subscriber + Send + Sync>),
}

impl Default for Logger {
	fn default() -> Self {
		Self::Sink
	}
}

impl std::fmt::Debug for Logger {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "Logger")
	}
}

impl From<Arc<dyn tracing::Subscriber + Send + Sync>> for Logger {
	fn from(value: Arc<dyn tracing::Subscriber + Send + Sync>) -> Self {
		Self::Logger(value)
	}
}
