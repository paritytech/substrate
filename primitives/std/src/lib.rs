// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Lowest-abstraction level for the Substrate runtime: just exports useful primitives from std
//! or client/alloc to be used with any code that depends on the runtime.

#![cfg_attr(not(feature = "std"), no_std)]


#![cfg_attr(feature = "std",
   doc = "Substrate runtime standard library as compiled when linked with Rust's standard library.")]
#![cfg_attr(not(feature = "std"),
   doc = "Substrate's runtime standard library as compiled without Rust's standard library.")]

#[macro_export]
macro_rules! map {
	($( $name:expr => $value:expr ),*) => (
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
	( $( $code:tt )* ) => {}
}

#[cfg(feature = "std")]
include!("../with_std.rs");

#[cfg(not(feature = "std"))]
include!("../without_std.rs");

/// Prelude of common useful imports.
///
/// This should include only things which are in the normal std prelude.
pub mod prelude {
	pub use crate::vec::Vec;
	pub use crate::boxed::Box;
	pub use crate::cmp::{Eq, PartialEq, Reverse};
	pub use crate::clone::Clone;

	// Re-export `vec!` macro here, but not in `std` mode, since
	// std's prelude already brings `vec!` into the scope.
	#[cfg(not(feature = "std"))]
	pub use crate::vec;
}
