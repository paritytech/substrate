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

//! # To allow tracing in WASM execution environment
//!
//! Facilitated by `sp_io::wasm_tracing`


/// This is holds a span id and is to signal on drop that a tracing span has exited
/// It must be bound to a named variable eg. `_span_guard`
pub struct TracingSpanGuard(pub u64);

impl Drop for TracingSpanGuard {
	fn drop(&mut self) {
		crate::sp_io::wasm_tracing::exit_span(self.0);
	}
}

/// Enters a tracing span, via [`sp_tracing::proxy`] measuring execution time
/// until exit from the current scope.
///
/// # Example
///
/// ```
/// wasm_tracing_span!("target", "fn_name");
/// ```
#[macro_export]
macro_rules! wasm_tracing_span {
	( $target:expr, $name:expr ) => {
		#[cfg(not(feature = "std"))]
		let __span_id__ = $crate::wasm_tracing::TracingSpanGuard(
			$crate::sp_io::wasm_tracing::enter_span($target, $name)
		);
	}
}