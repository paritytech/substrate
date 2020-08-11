// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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
//! To trace functions or invidual code in Substrate, this crate provides [`tracing_span`]
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
#![cfg_attr(not(feature = "std"), no_std)]

pub mod types;

#[cfg(not(feature = "std"))]
#[macro_export]
mod wasm_tracing;

#[cfg(feature = "std")]
use tracing;

#[cfg(feature = "std")]
pub use tracing::{
	span, event, Level
};

use sp_std::boxed::Box;
use core::sync::atomic::{AtomicBool, Ordering};
#[cfg(any(feature = "std", feature = "with-tracing"))]
use once_cell::sync::OnceCell;

/// Flag to signal whether to run wasm tracing
#[cfg(feature = "std")]
static WASM_TRACING_ENABLED: AtomicBool = AtomicBool::new(false);


pub use crate::types::{
	WasmMetadata, WasmAttributes, WasmValues, WasmEvent, WasmLevel,
};
#[cfg(not(feature = "std"))]
pub type Level = WasmLevel;

pub trait TracingSubscriber: Send + Sync {
	fn enabled(&self, metadata: WasmMetadata) -> bool;
	fn new_span(&self, attrs: WasmAttributes) -> u64;
	fn record(&self, span: u64, values: WasmValues);
	fn event(&self, event: WasmEvent);
	fn enter(&self, span: u64);
	fn exit(&self, span: u64);
}

/// Instance of the native subscriber in use
#[cfg(any(feature = "std", feature = "with-tracing"))]
static SUBSCRIBER_INSTANCE: OnceCell<Box<dyn TracingSubscriber>> = OnceCell::new();

/// Runs given code within a tracing span, measuring it's execution time.
///
/// If tracing is not enabled, the code is still executed.
///
/// # Example
///
/// ```
/// sp_tracing::tracing_span! {
///     "test-span";
///     1 + 1;
///     // some other complex code
/// }
/// ```
#[macro_export]
macro_rules! tracing_span {
	(
		$name:expr;
		$( $code:tt )*
	) => {
		{
			$crate::enter_span!($name);
			$( $code )*
		}
	}
}

/// Enter a span.
///
/// The span will be valid, until the scope is left.
///
/// # Example
///
/// ```
/// sp_tracing::enter_span!("test-span");
/// ```
#[macro_export]
macro_rules! enter_span {
	( $name:expr ) => {
		let __tracing_span__ = $crate::if_tracing!(
			$crate::span!($crate::Level::TRACE, $name)
		);
		// let __tracing_guard__ = $crate::if_tracing!(__tracing_span__.enter());
	}
}

/// Generates the given code if the tracing dependency is enabled.
#[macro_export]
#[cfg(feature = "std")]
macro_rules! if_tracing {
	( $if:expr ) => {{ $if }}
}

#[macro_export]
#[cfg(not(feature = "std"))]
macro_rules! if_tracing {
	( $if:expr ) => {{}}
}

#[cfg(feature = "std")]
pub fn wasm_tracing_enabled() -> bool {
	WASM_TRACING_ENABLED.load(Ordering::Relaxed)
}

#[cfg(feature = "std")]
pub fn set_wasm_tracing(b: bool) {
	WASM_TRACING_ENABLED.store(b, Ordering::Relaxed)
}

#[cfg(any(feature = "std", feature = "with-tracing"))]
pub fn set_tracing_subscriber(subscriber: Box<dyn TracingSubscriber>) {
	let _ = SUBSCRIBER_INSTANCE.set(subscriber);
}

#[cfg(any(feature = "std", feature = "with-tracing"))]
pub fn get_tracing_subscriber<'a>() -> Option<&'a Box<dyn TracingSubscriber>> {
	SUBSCRIBER_INSTANCE.get()
}


#[cfg(not(any(feature = "std", feature = "with-tracing")))]
pub fn get_tracing_subscriber<'a>() -> Option<&'a Box<dyn TracingSubscriber>> {
	None
}

#[cfg(not(any(feature = "std", feature = "with-tracing")))]
pub fn set_tracing_subscriber(subscriber: Box<dyn TracingSubscriber>) {
	unreachable!()
}