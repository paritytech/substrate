// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! Comprises the struct `ProxiedTrace` required by the proxy, encapsulates
//! the necessary associated unsafe code and provides a safe interface.

use std::pin::Pin;
use tracing::{span::Entered, Span};

/// Container for a proxied tracing Span and it's associated guard
pub struct ProxiedSpan {
	id: u64,
	// Note that `guard` and `span` must be declared in this order so that `guard` is dropped first.
	_guard: Entered<'static>,
	span: Pin<Box<Span>>,
}

impl ProxiedSpan {
	/// Enter the supplied span and return a new instance of ProxiedTrace containing it
	pub fn enter_span(id: u64, span: Pin<Box<Span>>) -> Self {
		// Transmute to static lifetime to enable guard to be stored
		// along with the span that it references
		let guard = unsafe {
			std::mem::transmute::<Entered<'_>, Entered<'static>>(span.enter())
		};

		ProxiedSpan {
			id,
			_guard: guard,
			span,
		}
	}

	/// Return copy of the span id
	pub fn id(&self) -> u64 {
		self.id
	}

	/// Return immutable reference to the span
	pub fn span(&self) -> &Span {
		&*self.span
	}
}
