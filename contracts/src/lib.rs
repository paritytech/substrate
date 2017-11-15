// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Temporary crate for contracts implementations.
//!
//! This will be replaced with WASM contracts stored on-chain.

#![warn(missing_docs)]

extern crate polkadot_primitives as primitives;
extern crate polkadot_serializer as serializer;
extern crate polkadot_state_machine as state_machine;
extern crate serde;

#[macro_use]
extern crate error_chain;
#[macro_use]
extern crate serde_derive;

#[cfg(test)]
#[macro_use]
extern crate assert_matches;

mod auth;
mod balances;
mod validator_set;

pub mod error;
pub mod executor;

/// Creates new RustExecutor for contracts.
pub fn executor() -> executor::RustExecutor {
	executor::RustExecutor::default()
}
