// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

// tag::description[]
//! Proc macro helpers for procedural macros
// end::description[]

extern crate syn;
#[macro_use]
extern crate quote;
extern crate proc_macro2;

extern crate proc_macro;

#[macro_use] extern crate srml_support_procedural_tools_derive;

// reexport proc macros
pub use srml_support_procedural_tools_derive::*;

pub mod syn_ext;

#[macro_export]
macro_rules! custom_keyword_impl {
  ($name:ident, $keyident:expr, $keydisp:expr) => {

    impl CustomKeyword for $name {
      fn ident() -> &'static str { $keyident }
      fn display() -> &'static str { $keydisp }
    }
  }
}

#[macro_export]
macro_rules! custom_keyword {
  ($name:ident, $keyident:expr, $keydisp:expr) => {

    #[derive(Debug)]
    struct $name;

    custom_keyword_impl!($name, $keyident, $keydisp);

  }
}



