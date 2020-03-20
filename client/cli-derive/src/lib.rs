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

//! Configuration trait for a CLI based on substrate

extern crate proc_macro;

mod spec_factory;
mod substrate_cli_params;

use proc_macro_error::proc_macro_error;

#[proc_macro_attribute]
#[proc_macro_error]
pub fn spec_factory(
	a: proc_macro::TokenStream,
	i: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
	spec_factory::spec_factory(a, i).into()
}

#[proc_macro_attribute]
#[proc_macro_error]
pub fn substrate_cli_params(
	a: proc_macro::TokenStream,
	i: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
	substrate_cli_params::substrate_cli_params(a, i).into()
}
