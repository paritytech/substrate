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

//! Macros to derive chain spec extension traits implementation.

mod impls;

use proc_macro::TokenStream;

#[proc_macro_derive(ChainSpecGroup)]
pub fn group_derive(input: TokenStream) -> TokenStream {
	match syn::parse(input) {
		Ok(ast) => impls::group_derive(&ast),
		Err(e) => e.to_compile_error().into(),
	}
}

#[proc_macro_derive(ChainSpecExtension, attributes(forks))]
pub fn extensions_derive(input: TokenStream) -> TokenStream {
	match syn::parse(input) {
		Ok(ast) => impls::extension_derive(&ast),
		Err(e) => e.to_compile_error().into(),
	}
}
