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

//! Provides the struct `ProxiedSpan`, which encapsulates the necessary
//! associated unsafe code and provides a safe interface to the proxy.

use std::mem::{transmute, ManuallyDrop};
use std::pin::Pin;
use tracing::{span::Entered, Span};

/// Container for a proxied tracing Span and it's associated guard
pub struct ProxiedSpan {
	id: u64,
	// Crucial that `guard` must be dropped first - ensured by `drop` impl.
	guard: ManuallyDrop<Entered<'static>>,
	span: ManuallyDrop<Pin<Box<Span>>>,
}

impl ProxiedSpan {
	/// Enter the supplied span and return a new instance of ProxiedTrace containing it
	pub fn enter_span(id: u64, span: Pin<Box<Span>>) -> Self {
		let span = ManuallyDrop::new(span);
		// Transmute to static lifetime to enable guard to be stored
		// along with the span that it references
		let guard = unsafe {
			ManuallyDrop::new(transmute::<Entered<'_>, Entered<'static>>(span.enter()))
		};

		ProxiedSpan {
			id,
			guard,
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

impl Drop for ProxiedSpan {
	fn drop(&mut self) {
		unsafe {
			// Ensure guard is dropped before span to prevent invalid reference
			ManuallyDrop::drop(&mut self.guard);
			ManuallyDrop::drop(&mut self.span);
		}
	}
}
