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
