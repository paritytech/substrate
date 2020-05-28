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

/// Indicates whether to run traces in wasm
pub static mut WASM_TRACING_ENABLED: bool = true;

/// This holds a tracing span id and is to signal on drop that a tracing span has exited.
/// It must be bound to a named variable eg. `_span_guard`.
///
/// 0 is a special inner value to indicate that the trace is disabled and should not call out
/// of the runtime.
pub struct TracingSpanGuard(Option<u64>);

impl TracingSpanGuard {
	pub fn new(span: Option<u64>) -> Self {
		Self(span)
	}
}

impl Drop for TracingSpanGuard {
	fn drop(&mut self) {
		if let Some(id) = self.0.take() {
			crate::sp_io::wasm_tracing::exit_span(id);
		}
	}
}

/// Enters a tracing span, via [`sp_tracing::proxy`] measuring execution time
/// until exit from the current scope.
///
/// It's also possible to directly call the functions `enter_span` and `exit_span`
/// in `sp_io::wasm_tracing` if more fine-grained control of span duration is required.
///
/// # Example
///
/// ```
/// frame_support::enter_span!("fn_name");
/// ```
#[macro_export]
macro_rules! enter_span {
	( $name:expr ) => {
		#[cfg(not(feature = "std"))]
		let __span_id__ = if unsafe { $crate::wasm_tracing::WASM_TRACING_ENABLED } {
				let id = $crate::sp_io::wasm_tracing::enter_span(
					module_path!(),
					$name
				);
				if id == 0 {
					unsafe { $crate::wasm_tracing::WASM_TRACING_ENABLED = false; }
					$crate::wasm_tracing::TracingSpanGuard::new(None)
				} else {
					$crate::wasm_tracing::TracingSpanGuard::new(Some(id))
				}
			} else {
				$crate::wasm_tracing::TracingSpanGuard::new(None)
			};
		#[cfg(feature = "std")]
		$crate::sp_tracing::enter_span!($name);
	}
}

