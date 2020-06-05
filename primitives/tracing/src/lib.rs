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

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
#[doc(hidden)]
pub use tracing;

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
			$crate::tracing::span!($crate::tracing::Level::TRACE, $name)
		);
		let __tracing_guard__ = $crate::if_tracing!(__tracing_span__.enter());
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
