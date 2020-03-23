// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Macros to derive runtime debug implementation.
//!
//! This custom derive implements a `core::fmt::Debug` trait,
//! but in case the `std` feature is enabled the implementation
//! will actually print out the structure as regular `derive(Debug)`
//! would do. If `std` is disabled the implementation will be empty.
//!
//! This behaviour is useful to prevent bloating the runtime WASM
//! blob from unneeded code.
//!
//! ```rust
//! #[derive(sp_debug_derive::RuntimeDebug)]
//!	struct MyStruct;
//!
//!	assert_eq!(format!("{:?}", MyStruct), "MyStruct");
//! ```

mod impls;

use proc_macro::TokenStream;

#[proc_macro_derive(RuntimeDebug)]
pub fn debug_derive(input: TokenStream) -> TokenStream {
   impls::debug_derive(syn::parse_macro_input!(input))
}

