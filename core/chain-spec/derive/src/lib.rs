// Copyright 2019 Parity Technologies (UK) Ltd.
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

extern crate proc_macro;

mod impls;

use proc_macro::TokenStream;

#[proc_macro_derive(ChainSpecGroup)]
pub fn group_derive(input: TokenStream) -> TokenStream {
	let ast = syn::parse(input).expect("Invalid AST");
	impls::group_derive(&ast)
}

#[proc_macro_derive(ChainSpecExtension)]
pub fn extensions_derive(input: TokenStream) -> TokenStream {
	let ast = syn::parse(input).expect("Invalid AST");
	impls::extension_derive(&ast)
}
