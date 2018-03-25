// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! The Substrate Demo runtime. This can be compiled with ``#[no_std]`, ready for Wasm.

#![cfg_attr(not(feature = "std"), no_std)]

#[allow(unused_imports)] #[macro_use] extern crate substrate_runtime_std as rstd;
#[macro_use] extern crate substrate_runtime_io as runtime_io;
#[macro_use] extern crate substrate_runtime_support as runtime_support;

extern crate substrate_runtime_primitives as runtime_primitives;

extern crate substrate_runtime_consensus as consensus;
extern crate substrate_runtime_executive as executive;
extern crate substrate_runtime_system as system;
extern crate substrate_runtime_timestamp as timestamp;

#[cfg(any(feature = "std", test))] extern crate substrate_keyring as keyring;
extern crate safe_mix;

#[cfg(feature = "std")] #[macro_use] extern crate serde_derive;
#[cfg(feature = "std")] extern crate serde;

#[cfg(feature = "std")] extern crate rustc_hex;

extern crate substrate_codec as codec;
#[cfg(feature = "std")] #[allow(unused_imports)] #[macro_use] extern crate substrate_primitives as primitives;
extern crate demo_primitives;

#[cfg(test)] #[macro_use] extern crate hex_literal;

extern crate integer_sqrt;

pub mod runtime;
pub mod block;
pub mod transaction;
pub mod api;

pub type Executive = executive::Executive<
	transaction::UncheckedTransaction,
	transaction::CheckedTransaction,
	runtime::Concrete,
	block::Block,
>;

//#[cfg(feature = "std")] pub mod genesismap;
