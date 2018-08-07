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

//! Defines primitive types for creating or validating a parachain.
//!
//! When compiled with standard library support, this crate exports a `wasm`
//! module that can be used to validate parachain WASM.
//!
//! ## Parachain WASM
//!
//! Polkadot parachain WASM is in the form of a module which imports a memory
//! instance and exports a function `validate`.
//!
//! `validate` accepts as input two `i32` values, representing a pointer/length pair
//! respectively, that encodes `ValidationParams`.
//!
//! `validate` returns an `i32` which is a pointer to a little-endian 32-bit integer denoting a length.
//! Subtracting the length from the initial pointer will give a new pointer to the actual return data,
//!
//! ASCII-diagram demonstrating the return data format:
//!
//! ```ignore
//! [return data][len (LE-u32)]
//!              ^~~returned pointer
//! ```
//!
//! The `load_params` and `write_result` functions provide utilities for setting up
//! a parachain WASM module in Rust.

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(alloc))]

/// Re-export of substrate-codec.
pub extern crate substrate_codec as codec;

#[macro_use]
extern crate substrate_codec_derive;

#[cfg(not(feature = "std"))]
extern crate alloc;

#[cfg(feature = "std")]
extern crate core;

#[cfg(feature = "std")]
extern crate wasmi;

#[cfg(feature = "std")]
#[macro_use]
extern crate error_chain;

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
use codec::{Encode, Decode};

#[cfg(feature = "std")]
pub mod wasm;

/// Validation parameters for evaluating the parachain validity function.
// TODO: consolidated ingress and balance downloads
#[derive(PartialEq, Eq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct ValidationParams {
	/// The collation body.
	pub block_data: Vec<u8>,
	/// Previous head-data.
	pub parent_head: Vec<u8>,
}

/// The result of parachain validation.
// TODO: egress and balance uploads
#[derive(PartialEq, Eq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct ValidationResult {
	/// New head data that should be included in the relay chain state.
	pub head_data: Vec<u8>
}

/// Load the validation params from memory when implementing a Rust parachain.
///
/// Offset and length must have been provided by the validation
/// function's entry point.
pub unsafe fn load_params(offset: usize, len: usize) -> ValidationParams {
	let mut slice = ::core::slice::from_raw_parts(offset as *const u8, len);

	ValidationParams::decode(&mut slice).expect("Invalid input data")
}

/// Allocate the validation result in memory, getting the return-pointer back.
///
/// As described in the crate docs, this is a pointer to the appended length
/// of the vector.
pub fn write_result(result: ValidationResult) -> usize {
	let mut encoded = result.encode();
	let len = encoded.len();

	assert!(len <= u32::max_value() as usize, "Len too large for parachain-WASM abi");
	(len as u32).using_encoded(|s| encoded.extend(s));

	// do not alter `encoded` beyond this point. may reallocate.
	let end_ptr = &encoded[len] as *const u8 as usize;

	// leak so it doesn't get zeroed.
	::core::mem::forget(encoded);
	end_ptr
}
