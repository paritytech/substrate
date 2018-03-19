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
#[cfg(any(feature = "std", test))] extern crate substrate_keyring as keyring;

#[cfg(feature = "std")] #[macro_use] extern crate serde_derive;
#[cfg(feature = "std")] extern crate serde;

#[cfg(feature = "std")] extern crate rustc_hex;

extern crate substrate_codec as codec;
#[cfg(feature = "std")] #[macro_use] extern crate substrate_primitives as primitives;
extern crate demo_primitives;

#[cfg(test)] #[macro_use] extern crate hex_literal;

extern crate integer_sqrt;

#[macro_use] pub mod dispatch;

pub mod block;
pub mod transaction;
pub mod environment;
pub mod runtime;
pub mod api;

#[cfg(feature = "std")] pub mod genesismap;
