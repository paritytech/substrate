// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Lowest-abstraction level for the Substrate runtime: just exports useful primitives from std
//! or client/alloc to be used with any code that depends on the runtime.

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(
	feature = "std",
	doc = "Substrate runtime standard library as compiled when linked with Rust's standard library."
)]
#![cfg_attr(
	not(feature = "std"),
	doc = "Substrate's runtime standard library as compiled without Rust's standard library."
)]

/// Initialize a key-value collection from array.
///
/// Creates a vector of given pairs and calls `collect` on the iterator from it.
/// Can be used to create a `HashMap`.
#[macro_export]
macro_rules! map {
	($( $name:expr => $value:expr ),* $(,)? ) => (
		vec![ $( ( $name, $value ) ),* ].into_iter().collect()
	)
}

/// Feature gate some code that should only be run when `std` feature is enabled.
///
/// # Example
///
/// ```
/// use sp_std::if_std;
///
/// if_std! {
///     // This code is only being compiled and executed when the `std` feature is enabled.
///     println!("Hello native world");
/// }
/// ```
#[cfg(feature = "std")]
#[macro_export]
macro_rules! if_std {
	( $( $code:tt )* ) => {
		$( $code )*
	}
}

#[cfg(not(feature = "std"))]
#[macro_export]
macro_rules! if_std {
	( $( $code:tt )* ) => {};
}

#[cfg(feature = "std")]
include!("../with_std.rs");

#[cfg(not(feature = "std"))]
include!("../without_std.rs");

/// A target for `core::write!` macro - constructs a string in memory.
#[derive(Default)]
pub struct Writer(vec::Vec<u8>);

impl fmt::Write for Writer {
	fn write_str(&mut self, s: &str) -> fmt::Result {
		self.0.extend(s.as_bytes());
		Ok(())
	}
}

impl Writer {
	/// Access the content of this `Writer` e.g. for printout
	pub fn inner(&self) -> &vec::Vec<u8> {
		&self.0
	}

	/// Convert into the content of this `Writer`
	pub fn into_inner(self) -> vec::Vec<u8> {
		self.0
	}
}

/// Prelude of common useful imports.
///
/// This should include only things which are in the normal std prelude.
pub mod prelude {
	pub use crate::{
		boxed::Box,
		clone::Clone,
		cmp::{Eq, PartialEq, Reverse},
		convert::{TryFrom, TryInto},
		iter::IntoIterator,
		vec::Vec,
	};

	// Re-export `vec!` macro here, but not in `std` mode, since
	// std's prelude already brings `vec!` into the scope.
	#[cfg(not(feature = "std"))]
	pub use crate::vec;
}
