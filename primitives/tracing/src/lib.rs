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

#[cfg(feature = "with-tracing")]
use core::{module_path, format_args};

#[cfg(feature = "std")]
#[macro_use]
extern crate rental;

#[cfg(feature = "with-tracing")]
#[doc(hidden)]
pub use tracing;

#[cfg(feature = "with-tracing")]
pub use tracing::Level;

#[cfg(feature = "std")]
pub mod proxy;

#[cfg(feature = "std")]
use std::sync::atomic::{AtomicBool, Ordering};

/// Flag to signal whether to run wasm tracing
#[cfg(feature = "std")]
static WASM_TRACING_ENABLED: AtomicBool = AtomicBool::new(false);

/// Runs given code within a tracing span, measuring it's execution time.
///
/// If tracing is not enabled, the code is still executed.
///
/// # Example
///
/// ```
/// sp_tracing::tracing_span! { // default level LEVEL:TRACE
///     "test-span";
///     1 + 1;
///     // some other complex code
/// }
///
/// sp_tracing::tracing_span! { // specified log level
///		Level::DEBUG,
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
	};
	(
		$lvl:expr,
		$name:expr;
		$( $code:tt )*
	) => {
		{
			$crate::enter_span!($lvl, $name);
			$( $code )*
		}
	};
}

/// Enter a span.
///
/// The span will be valid, until the scope is left.  noop unless `with-tracing`-feature is enabled
///
/// # Example
///
/// ```
/// sp_tracing::enter_span!("test-span"); // defaults to Level::TRACE
/// sp_tracing::enter_span!(sp_tracing::Level::DEBUG, "debug-span");
/// ```
#[macro_export]
#[cfg(feature = "with-tracing")]
macro_rules! enter_span {
	( $name:expr ) => ({
		$crate::enter_span!($crate::tracing::Level::TRACE, $name);
	});
	( $lvl:expr, $name:expr ) => ({
		// FIXME: we need to make the variable names based on $name or they might overlap
		let __tracing_span__ = $crate::tracing::span!($lvl, $name);
		let __tracing_guard__ = __tracing_span__.enter();
	});
}


/// Enter a span.
///
/// The span will be valid, until the scope is left. noop unless `with-tracing`-feature is enabled
///
/// # Example
///
/// ```
/// sp_tracing::enter_span!("test-span"); // defaults to Level::TRACE
/// sp_tracing::enter_span!(sp_tracing::Level::DEBUG, "debug-span");
/// ```
#[macro_export]
#[cfg(not(feature = "with-tracing"))]
macro_rules! enter_span {
	( $name:expr ) => ({ {} });
	( $lvl:expr, $name:expr ) => ({ {} });
}

/// Trace an Event.
///
/// see `tracing`-crate for details on usage
/// noop if `with-tracing`-feature is not enabled.
#[macro_export]
#[cfg(feature = "with-tracing")]
macro_rules! event {

    (target: $target:expr, parent: $parent:expr, $lvl:expr, { $($fields:tt)* } )=> ({
		$crate::tracing::event!(target: $target:expr, parent: $parent:expr, $lvl:expr, { $($k).+ = $($fields)* })
	});

    (target: $target:expr, parent: $parent:expr, $lvl:expr, { $($fields:tt)* }, $($arg:tt)+ ) => ({
        $crate::tracing::event!(
            target: $target,
            parent: $parent,
            $lvl,
            { message = format_args!($($arg)+), $($fields)* }
        )
    });
    (target: $target:expr, parent: $parent:expr, $lvl:expr, $($k:ident).+ = $($fields:tt)* ) => (
        $crate::tracing::event!(target: $target, parent: $parent, $lvl, { $($k).+ = $($fields)* })
    );
    (target: $target:expr, parent: $parent:expr, $lvl:expr, $($arg:tt)+) => (
        $crate::tracing::event!(target: $target, parent: $parent, $lvl, { $($arg)+ })
    );
    (target: $target:expr, $lvl:expr, { $($fields:tt)* } )=> ({
        $crate::tracing::event!(target: $target, $lvl, { $($k).+ = $($fields)* })
    });
    (target: $target:expr, $lvl:expr, { $($fields:tt)* }, $($arg:tt)+ ) => ({
        $crate::tracing::event!(
            target: $target,
            $lvl,
            { message = format_args!($($arg)+), $($fields)* }
        )
    });
    (target: $target:expr, $lvl:expr, $($k:ident).+ = $($fields:tt)* ) => (
        $crate::tracing::event!(target: $target, $lvl, { $($k).+ = $($fields)* })
    );
    (target: $target:expr, $lvl:expr, $($arg:tt)+ ) => (
        $crate::tracing::event!(target: $target, $lvl, { $($arg)+ })
    );
    (parent: $parent:expr, $lvl:expr, { $($fields:tt)* }, $($arg:tt)+ ) => (
        $crate::tracing::event!(
            target: module_path!(),
            parent: $parent,
            $lvl,
            { message = format_args!($($arg)+), $($fields)* }
        )
    );
    (parent: $parent:expr, $lvl:expr, { $($fields:tt)* }, $($arg:tt)+ ) => (
        $crate::tracing::event!(
            target: module_path!(),
            $lvl,
            parent: $parent,
            { message = format_args!($($arg)+), $($fields)* }
        )
    );
    (parent: $parent:expr, $lvl:expr, $($k:ident).+ = $($field:tt)*) => (
        $crate::tracing::event!(
            target: module_path!(),
            parent: $parent,
            $lvl,
            { $($k).+ = $($field)*}
        )
    );
    (parent: $parent:expr, $lvl:expr, ?$($k:ident).+ = $($field:tt)*) => (
        $crate::tracing::event!(
            target: module_path!(),
            parent: $parent,
            $lvl,
            { ?$($k).+ = $($field)*}
        )
    );
    (parent: $parent:expr, $lvl:expr, %$($k:ident).+ = $($field:tt)*) => (
        $crate::tracing::event!(
            target: module_path!(),
            parent: $parent,
            $lvl,
            { %$($k).+ = $($field)*}
        )
    );
    (parent: $parent:expr, $lvl:expr, $($k:ident).+, $($field:tt)*) => (
        $crate::tracing::event!(
            target: module_path!(),
            parent: $parent,
            $lvl,
            { $($k).+, $($field)*}
        )
    );
    (parent: $parent:expr, $lvl:expr, %$($k:ident).+, $($field:tt)*) => (
        $crate::tracing::event!(
            target: module_path!(),
            parent: $parent,
            $lvl,
            { %$($k).+, $($field)*}
        )
    );
    (parent: $parent:expr, $lvl:expr, ?$($k:ident).+, $($field:tt)*) => (
        $crate::tracing::event!(
            target: module_path!(),
            parent: $parent,
            $lvl,
            { ?$($k).+, $($field)*}
        )
    );
    (parent: $parent:expr, $lvl:expr, $($arg:tt)+ ) => (
        $crate::tracing::event!(target: module_path!(), parent: $parent, $lvl, { $($arg)+ })
    );
    ( $lvl:expr, { $($fields:tt)* }, $($arg:tt)+ ) => (
        $crate::tracing::event!(
            target: module_path!(),
            $lvl,
            { message = format_args!($($arg)+), $($fields)* }
        )
    );
    ( $lvl:expr, { $($fields:tt)* }, $($arg:tt)+ ) => (
        $crate::tracing::event!(
            target: module_path!(),
            $lvl,
            { message = format_args!($($arg)+), $($fields)* }
        )
    );
    ($lvl:expr, $($k:ident).+ = $($field:tt)*) => (
        $crate::tracing::event!(
            target: module_path!(),
            $lvl,
            { $($k).+ = $($field)*}
        )
    );
    ($lvl:expr, $($k:ident).+, $($field:tt)*) => (
        $crate::tracing::event!(
            target: module_path!(),
            $lvl,
            { $($k).+, $($field)*}
        )
    );
    ($lvl:expr, ?$($k:ident).+, $($field:tt)*) => (
        $crate::tracing::event!(
            target: module_path!(),
            $lvl,
            { ?$($k).+, $($field)*}
        )
    );
    ($lvl:expr, %$($k:ident).+, $($field:tt)*) => (
        $crate::tracing::event!(
            target: module_path!(),
            $lvl,
            { %$($k).+, $($field)*}
        )
    );
    ($lvl:expr, ?$($k:ident).+) => (
        $crate::tracing::event!($lvl, ?$($k).+,)
    );
    ($lvl:expr, %$($k:ident).+) => (
        $crate::tracing::event!($lvl, %$($k).+,)
    );
    ($lvl:expr, $($k:ident).+) => (
        $crate::tracing::event!($lvl, $($k).+,)
    );
    ( $lvl:expr, $($arg:tt)+ ) => (
        $crate::tracing::event!(target: module_path!(), $lvl, { $($arg)+ })
    );

    (target: $target:expr, parent: $parent:expr, $lvl:expr, { $($fields:tt)* }, $($arg:tt)+ ) => ({
		$crate::tracing::event!(target: $target:expr, parent: $parent:expr, $lvl:expr, { $($k).+ = $($fields)* }, { $($arg)+ })
	});
	
    (target: $target:expr, parent: $parent:expr, $lvl:expr, $($k:ident).+ = $($fields:tt)* ) => (
        $crate::tracing::event!(target: $target, parent: $parent, $lvl, { $($k).+ = $($fields)* })
    );
    (target: $target:expr, parent: $parent:expr, $lvl:expr, $($arg:tt)+) => (
        $crate::tracing::event!(target: $target, parent: $parent, $lvl, { $($arg)+ })
    );
    (target: $target:expr, $lvl:expr, { $($fields:tt)* } )=> ({
        $crate::tracing::event!(target: $target, parent: $parent, $lvl, { $($k).+ = $($fields)* })
    });
    (target: $target:expr, $lvl:expr, { $($fields:tt)* }, $($arg:tt)+ ) => ({
        $crate::tracing::event!(
            target: $target,
			$lvl,
			{ $($k).+ = $($fields)* },
			{ $($arg)+ }
        )
    });
    (target: $target:expr, $lvl:expr, $($k:ident).+ = $($fields:tt)* ) => (
        $crate::tracing::event!(target: $target, $lvl, { $($k).+ = $($fields)* })
    );
    (target: $target:expr, $lvl:expr, $($arg:tt)+ ) => (
        $crate::tracing::event!(target: $target, $lvl, { $($arg)+ })
    );
    (parent: $parent:expr, $lvl:expr, { $($fields:tt)* }, $($arg:tt)+ ) => (
        $crate::tracing::event!(
            parent: $parent,
			$lvl,
			{ $($k).+ = $($fields)* },
			{ $($arg)+ }
        )
    );
    (parent: $parent:expr, $lvl:expr, { $($fields:tt)* }, $($arg:tt)+ ) => (
        $crate::tracing::event!(
            $lvl,
            parent: $parent,
			{ $($k).+ = $($fields)* },
			{ $($arg)+ }
        )
    );
    (parent: $parent:expr, $lvl:expr, $($k:ident).+ = $($field:tt)*) => (
        $crate::tracing::event!(
            parent: $parent,
            $lvl,
            { $($k).+ = $($field)*}
        )
    );
    (parent: $parent:expr, $lvl:expr, ?$($k:ident).+ = $($field:tt)*) => (
        $crate::tracing::event!(
            parent: $parent,
            $lvl,
            { ?$($k).+ = $($field)*}
        )
    );
    (parent: $parent:expr, $lvl:expr, %$($k:ident).+ = $($field:tt)*) => (
        $crate::tracing::event!(
            parent: $parent,
            $lvl,
            { %$($k).+ = $($field)*}
        )
    );
    (parent: $parent:expr, $lvl:expr, $($k:ident).+, $($field:tt)*) => (
        $crate::tracing::event!(
            parent: $parent,
            $lvl,
            { $($k).+, $($field)*}
        )
    );
    (parent: $parent:expr, $lvl:expr, %$($k:ident).+, $($field:tt)*) => (
        $crate::tracing::event!(
            parent: $parent,
            $lvl,
            { %$($k).+, $($field)*}
        )
    );
    (parent: $parent:expr, $lvl:expr, ?$($k:ident).+, $($field:tt)*) => (
        $crate::tracing::event!(
            parent: $parent,
            $lvl,
            { ?$($k).+, $($field)*}
        )
    );
    (parent: $parent:expr, $lvl:expr, $($arg:tt)+ ) => (
        $crate::tracing::event!(parent: $parent, $lvl, { $($arg)+ })
    );
    ( $lvl:expr, { $($fields:tt)* }, $($arg:tt)+ ) => (
        $crate::tracing::event!(
            $lvl,
            { $($arg)+, $($fields)* }
        )
    );
    ( $lvl:expr, { $($fields:tt)* }, $($arg:tt)+ ) => (
        $crate::tracing::event!(
            $lvl,
            { $($arg)+, $($fields)* }
        )
    );
    ($lvl:expr, $($k:ident).+ = $($field:tt)*) => (
        $crate::tracing::event!(
            $lvl,
            { $($k).+ = $($field)*}
        )
    );
    ($lvl:expr, $($k:ident).+, $($field:tt)*) => (
        $crate::tracing::event!(
            $lvl,
            { $($k).+, $($field)*}
        )
    );
    ($lvl:expr, ?$($k:ident).+, $($field:tt)*) => (
        $crate::tracing::event!(
            $lvl,
            { ?$($k).+, $($field)*}
        )
    );
    ($lvl:expr, %$($k:ident).+, $($field:tt)*) => (
        $crate::tracing::event!(
            $lvl,
            { %$($k).+, $($field)*}
        )
    );
    ($lvl:expr, ?$($k:ident).+) => (
        $crate::tracing::event!($lvl, ?$($k).+,)
    );
    ($lvl:expr, %$($k:ident).+) => (
        $crate::tracing::event!($lvl, %$($k).+,)
    );
    ($lvl:expr, $($k:ident).+) => (
        $crate::tracing::event!($lvl, $($k).+,)
    );
    ( $lvl:expr, $($arg:tt)+ ) => (
        $crate::tracing::event!($lvl, { $($arg)+ })
    );
}

/// Trace an Event.
///
/// see `tracing`-crate for details on usage
/// noop if `with-tracing`-feature is not enabled.
#[macro_export]
#[cfg(not(feature = "with-tracing"))]
macro_rules! event {
    (target: $target:expr, parent: $parent:expr, $lvl:expr, { $($fields:tt)* } )=> ({ {} });
    (target: $target:expr, parent: $parent:expr, $lvl:expr, { $($fields:tt)* }, $($arg:tt)+ ) => ({ {} });
    (target: $target:expr, parent: $parent:expr, $lvl:expr, $($k:ident).+ = $($fields:tt)* ) => ({ {} });
    (target: $target:expr, parent: $parent:expr, $lvl:expr, $($arg:tt)+) => ({ {} });
    (target: $target:expr, $lvl:expr, { $($fields:tt)* } )=> ({ {} });
    (target: $target:expr, $lvl:expr, { $($fields:tt)* }, $($arg:tt)+ ) => ({ {} });
    (target: $target:expr, $lvl:expr, $($k:ident).+ = $($fields:tt)* ) => ({ {} });
    (target: $target:expr, $lvl:expr, $($arg:tt)+ ) => ({ {} });
    (parent: $parent:expr, $lvl:expr, { $($fields:tt)* }, $($arg:tt)+ ) => ({ {} });
    (parent: $parent:expr, $lvl:expr, { $($fields:tt)* }, $($arg:tt)+ ) => ({ {} });
    (parent: $parent:expr, $lvl:expr, $($k:ident).+ = $($field:tt)*) => ({ {} });
    (parent: $parent:expr, $lvl:expr, ?$($k:ident).+ = $($field:tt)*) => ({ {} });
    (parent: $parent:expr, $lvl:expr, %$($k:ident).+ = $($field:tt)*) => ({ {} });
    (parent: $parent:expr, $lvl:expr, $($k:ident).+, $($field:tt)*) => ({ {} });
    (parent: $parent:expr, $lvl:expr, %$($k:ident).+, $($field:tt)*) => ({ {} });
    (parent: $parent:expr, $lvl:expr, ?$($k:ident).+, $($field:tt)*) => ({ {} });
    (parent: $parent:expr, $lvl:expr, $($arg:tt)+ ) => ({ {} });
    ($lvl:expr, { $($fields:tt)* }, $($arg:tt)+ ) => ({ {} });
    ($lvl:expr, { $($fields:tt)* }, $($arg:tt)+ ) => ({ {} });
    ($lvl:expr, $($k:ident).+ = $($field:tt)*) => ({ {} });
    ($lvl:expr, $($k:ident).+, $($field:tt)*) => ({ {} });
    ($lvl:expr, ?$($k:ident).+, $($field:tt)*) => ({ {} });
    ($lvl:expr, %$($k:ident).+, $($field:tt)*) => ({ {} });
    ($lvl:expr, ?$($k:ident).+) => ({ {} });
    ($lvl:expr, %$($k:ident).+) => ({ {} });
    ($lvl:expr, $($k:ident).+) => ({ {} });
    ($lvl:expr, $($arg:tt)+ ) => ({ {} });
}

#[cfg(feature = "std")]
pub fn wasm_tracing_enabled() -> bool {
	WASM_TRACING_ENABLED.load(Ordering::Relaxed)
}

#[cfg(feature = "std")]
pub fn set_wasm_tracing(b: bool) {
	WASM_TRACING_ENABLED.store(b, Ordering::Relaxed)
}