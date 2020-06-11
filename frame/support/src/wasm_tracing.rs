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

// static mut has potential for data race conditions.
// For current use-case this is not an issue, must only be used in wasm
#[cfg(not(feature = "std"))]
static mut WASM_TRACING_ENABLED: bool = true;

/// Indicates whether to run traces in wasm
#[cfg(not(feature = "std"))]
pub fn wasm_tracing_enabled() -> bool {
	unsafe { WASM_TRACING_ENABLED }
}

/// Disable wasm traces
#[cfg(not(feature = "std"))]
pub fn disable_wasm_tracing() {
	unsafe { WASM_TRACING_ENABLED = false }
}

/// This holds a tracing span id and is to signal on drop that a tracing span has exited.
/// It must be bound to a named variable eg. `_span_guard`.
#[cfg(not(feature = "std"))]
pub struct TracingSpanGuard(Option<u64>);

#[cfg(not(feature = "std"))]
impl TracingSpanGuard {
	pub fn new(span: Option<u64>) -> Self {
		Self(span)
	}
}

#[cfg(not(feature = "std"))]
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
		let __span_id__ = if $crate::wasm_tracing::wasm_tracing_enabled() {
				let id = $crate::sp_io::wasm_tracing::enter_span(
					module_path!(),
					$name
				);
				if id == 0 {
					$crate::wasm_tracing::disable_wasm_tracing();
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

