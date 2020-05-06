// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

//! Macros for declaring and implementing runtime apis.

#![recursion_limit = "512"]

use proc_macro::TokenStream;

mod impl_runtime_apis;
mod mock_impl_runtime_apis;
mod decl_runtime_apis;
mod utils;

#[proc_macro]
pub fn impl_runtime_apis(input: TokenStream) -> TokenStream {
	impl_runtime_apis::impl_runtime_apis_impl(input)
}

#[proc_macro]
pub fn mock_impl_runtime_apis(input: TokenStream) -> TokenStream {
	mock_impl_runtime_apis::mock_impl_runtime_apis_impl(input)
}

#[proc_macro]
pub fn decl_runtime_apis(input: TokenStream) -> TokenStream {
	decl_runtime_apis::decl_runtime_apis_impl(input)
}
