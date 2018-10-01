// Copyright 2018 Parity Technologies (UK) Ltd.
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
//! Substrate transaction pool.
// end::description[]

#![warn(missing_docs)]
#![warn(unused_extern_crates)]

extern crate parity_codec;
extern crate sr_primitives;
extern crate substrate_client as client;
extern crate substrate_primitives;

pub extern crate substrate_transaction_graph as txpool;

#[macro_use]
extern crate error_chain;

#[cfg(test)]
extern crate substrate_test_client as test_client;
#[cfg(test)]
extern crate substrate_keyring as keyring;

mod api;
#[cfg(test)]
mod tests;

pub mod error;

pub use api::ChainApi;
