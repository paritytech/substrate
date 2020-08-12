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

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(once_cell))]

mod types;

#[cfg(no_std)]
#[macro_export]
mod wasm_tracing;

#[cfg(not(no_std))]
use tracing;

#[cfg(not(no_std))]
pub use tracing::{
	debug, debug_span, error, error_span, info, info_span, trace, trace_span, warn, warn_span,
	span, event, Level
};

#[cfg(all(no_std, feature = "with-tracing"))]
use sp_std::boxed::Box;

#[cfg(all(no_std, feature = "with-tracing"))]
use core::lazy::OnceCell;

pub use crate::types::{
	WasmMetadata, WasmAttributes, WasmValues, WasmEvent, WasmLevel,
};
#[cfg(no_std)]
pub type Level = WasmLevel;

#[cfg(no_std)]
pub trait TracingSubscriber: Send + Sync {
	fn enabled(&self, metadata: WasmMetadata) -> bool;
	fn new_span(&self, attrs: WasmAttributes) -> u64;
	fn record(&self, span: u64, values: WasmValues);
	fn event(&self, event: WasmEvent);
	fn enter(&self, span: u64);
	fn exit(&self, span: u64);
}

/// Instance of the native subscriber in use
#[cfg(all(no_std, feature = "with-tracing"))]
static SUBSCRIBER_INSTANCE: OnceCell<Box<dyn TracingSubscriber>> = OnceCell::new();

/// Runs given code within a tracing span, measuring it's execution time.
///
/// If tracing is not enabled, the code is still executed.
///
/// # Example
///
/// ```
/// sp_tracing::within_span! {
///     "test-span";
///     1 + 1;
///     // some other complex code
/// }
/// ```
#[cfg(any(not(no_std), not(feature = "with-tracing")))]
#[macro_export]
macro_rules! within_span {
	(
		$span:expr;
		$( $code:tt )*
	) => {
		{
			$crate::enter_span!($span);
			$( $code )*
		}
	};
	(
		$lvl:expr,
		$name:expr;
		$( $code:tt )*
	) => {
		{
			$crate::within_span!($crate::span!($crate::Level::TRACE, $name); $( $code )*)
		}
	};
}

#[cfg(all(no_std, not(feature = "with-tracing")))]
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


#[cfg(all(no_std, not(feature = "with-tracing")))]
#[macro_export]
macro_rules! enter_span {
	( $lvl:expr, $name:expr ) => { },
	( $name:expr ) => {  } // no-op
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
#[cfg(any(not(no_std), not(feature = "with-tracing")))]
#[macro_export]
macro_rules! enter_span {
	( $span:expr ) => {
		// FIXME: this could be clashing, make the local variable based on name to prevent that
		let __within_span__ = $span;
		let __tracing_guard__ = __within_span__.enter();
	};
	( $lvl:expr, $name:expr ) => {
		$crate::enter_span!($crate::span!($crate::Level::TRACE, $name))
	};
}

#[cfg(all(no_std, feature = "with-tracing"))]
pub fn set_tracing_subscriber(subscriber: Box<dyn TracingSubscriber>) {
	let _ = SUBSCRIBER_INSTANCE.set(subscriber);
}

#[cfg(all(no_std, feature = "with-tracing"))]
pub fn get_tracing_subscriber<'a>() -> Option<&'a Box<dyn TracingSubscriber>> {
	SUBSCRIBER_INSTANCE.get()
}


#[cfg(all(no_std, not(feature = "with-tracing")))]
pub fn get_tracing_subscriber<'a>() -> Option<&'a Box<dyn TracingSubscriber>> {
	None
}

#[cfg(all(no_std, not(feature = "with-tracing")))]
pub fn set_tracing_subscriber(_subscriber: Box<dyn TracingSubscriber>) {
	unreachable!()
}