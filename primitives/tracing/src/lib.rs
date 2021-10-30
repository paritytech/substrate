// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Substrate tracing primitives and macros.
//!
//! To trace functions or invidual code in Substrate, this crate provides [`within_span`]
//! and [`enter_span`]. See the individual docs for how to use these macros.
//!
//! Note that to allow traces from wasm execution environment there are
//! 2 reserved identifiers for tracing `Field` recording, stored in the consts:
//! `WASM_TARGET_KEY` and `WASM_NAME_KEY` - if you choose to record fields, you
//! must ensure that your identifiers do not clash with either of these.
//!
//! Additionally, we have a const: `WASM_TRACE_IDENTIFIER`, which holds a span name used
//! to signal that the 'actual' span name and target should be retrieved instead from
//! the associated Fields mentioned above.
//!
//! Note: The `tracing` crate requires trace metadata to be static. This does not work
//! for wasm code in substrate, as it is regularly updated with new code from on-chain
//! events. The workaround for this is for the wasm tracing wrappers to put the
//! `name` and `target` data in the `values` map (normally they would be in the static
//! metadata assembled at compile time).

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
use tracing;
pub use tracing::{
	debug, debug_span, error, error_span, event, info, info_span, span, trace, trace_span, warn,
	warn_span, Level, Span,
};

pub use crate::types::{
	WasmEntryAttributes, WasmFieldName, WasmFields, WasmLevel, WasmMetadata, WasmValue,
	WasmValuesSet,
};
#[cfg(feature = "std")]
pub use crate::types::{WASM_NAME_KEY, WASM_TARGET_KEY, WASM_TRACE_IDENTIFIER};

/// Tracing facilities and helpers.
///
/// This is modeled after the `tracing`/`tracing-core` interface and uses that more or
/// less directly for the native side. Because of certain optimisations the these crates
/// have done, the wasm implementation diverges slightly and is optimised for that use
/// case (like being able to cross the wasm/native boundary via scale codecs).
///
/// One of said optimisations is that all macros will yield to a `noop` in non-std unless
/// the `with-tracing` feature is explicitly activated. This allows you to just use the
/// tracing wherever you deem fit and without any performance impact by default. Only if
/// the specific `with-tracing`-feature is activated on this crate will it actually include
/// the tracing code in the non-std environment.
///
/// Because of that optimisation, you should not use the `span!` and `span_*!` macros
/// directly as they yield nothing without the feature present. Instead you should use
/// `enter_span!` and `within_span!` – which would strip away even any parameter conversion
/// you do within the span-definition (and thus optimise your performance). For your
/// convineience you directly specify the `Level` and name of the span or use the full
/// feature set of `span!`/`span_*!` on it:
///
/// # Example
///
/// ```rust
/// sp_tracing::enter_span!(sp_tracing::Level::TRACE, "fn wide span");
/// {
/// 		sp_tracing::enter_span!(sp_tracing::trace_span!("outer-span"));
/// 		{
/// 			sp_tracing::enter_span!(sp_tracing::Level::TRACE, "inner-span");
/// 			// ..
/// 		}  // inner span exists here
/// 	} // outer span exists here
///
/// sp_tracing::within_span! {
/// 		sp_tracing::debug_span!("debug-span", you_can_pass="any params");
///     1 + 1;
///     // some other complex code
/// } // debug span ends here
/// ```
///
///
/// # Setup
///
/// This project only provides the macros and facilities to manage tracing
/// it doesn't implement the tracing subscriber or backend directly – that is
/// up to the developer integrating it into a specific environment. In native
/// this can and must be done through the regular `tracing`-facitilies, please
/// see their documentation for details.
///
/// On the wasm-side we've adopted a similar approach of having a global
/// `TracingSubscriber` that the macros call and that does the actual work
/// of tracking. To provide your tracking, you must implement `TracingSubscriber`
/// and call `set_tracing_subscriber` at the very beginning of your execution –
/// the default subscriber is doing nothing, so any spans or events happening before
/// will not be recorded!
mod types;

/// Try to init a simple tracing subscriber with log compatibility layer.
/// Ignores any error. Useful for testing.
#[cfg(feature = "std")]
pub fn try_init_simple() {
	let _ = tracing_subscriber::fmt()
		.with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
		.with_writer(std::io::stderr)
		.try_init();
}

/// Runs given code within a tracing span, measuring it's execution time.
///
/// If tracing is not enabled, the code is still executed. Pass in level and name or
/// use any valid `sp_tracing::Span`followe by `;` and the code to execute,
///
/// # Example
///
/// ```
/// sp_tracing::within_span! {
/// 		sp_tracing::Level::TRACE,
///     "test-span";
///     1 + 1;
///     // some other complex code
/// }
///
/// sp_tracing::within_span! {
/// 		sp_tracing::span!(sp_tracing::Level::WARN, "warn-span", you_can_pass="any params");
///     1 + 1;
///     // some other complex code
/// }
///
/// sp_tracing::within_span! {
/// 		sp_tracing::debug_span!("debug-span", you_can_pass="any params");
///     1 + 1;
///     // some other complex code
/// }
/// ```
#[cfg(any(feature = "std", feature = "with-tracing"))]
#[macro_export]
macro_rules! within_span {
	(
		$span:expr;
		$( $code:tt )*
	) => {
		$span.in_scope(||
			{
				$( $code )*
			}
		)
	};
	(
		$lvl:expr,
		$name:expr;
		$( $code:tt )*
	) => {
		{
			$crate::within_span!($crate::span!($lvl, $name); $( $code )*)
		}
	};
}

#[cfg(all(not(feature = "std"), not(feature = "with-tracing")))]
#[macro_export]
macro_rules! within_span {
	(
		$span:stmt;
		$( $code:tt )*
	) => {
		$( $code )*
	};
	(
		$lvl:expr,
		$name:expr;
		$( $code:tt )*
	) => {
		$( $code )*
	};
}

/// Enter a span - noop for `no_std` without `with-tracing`
#[cfg(all(not(feature = "std"), not(feature = "with-tracing")))]
#[macro_export]
macro_rules! enter_span {
	( $lvl:expr, $name:expr ) => {};
	( $name:expr ) => {}; // no-op
}

/// Enter a span.
///
/// The span will be valid, until the scope is left. Use either level and name
/// or pass in any valid `sp_tracing::Span` for extended usage. The span will
/// be exited on drop – which is at the end of the block or to the next
/// `enter_span!` calls, as this overwrites the local variable. For nested
/// usage or to ensure the span closes at certain time either put it into a block
/// or use `within_span!`
///
/// # Example
///
/// ```
/// sp_tracing::enter_span!(sp_tracing::Level::TRACE, "test-span");
/// // previous will be dropped here
/// sp_tracing::enter_span!(
/// 	sp_tracing::span!(sp_tracing::Level::DEBUG, "debug-span", params="value"));
/// sp_tracing::enter_span!(sp_tracing::info_span!("info-span",  params="value"));
///
/// {
/// 		sp_tracing::enter_span!(sp_tracing::Level::TRACE, "outer-span");
/// 		{
/// 			sp_tracing::enter_span!(sp_tracing::Level::TRACE, "inner-span");
/// 			// ..
/// 		}  // inner span exists here
/// 	} // outer span exists here
/// ```
#[cfg(any(feature = "std", feature = "with-tracing"))]
#[macro_export]
macro_rules! enter_span {
	( $span:expr ) => {
		// Calling this twice in a row will overwrite (and drop) the earlier
		// that is a _documented feature_!
		let __within_span__ = $span;
		let __tracing_guard__ = __within_span__.enter();
	};
	( $lvl:expr, $name:expr ) => {
		$crate::enter_span!($crate::span!($lvl, $name))
	};
}
