// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use sp_std::vec::Vec;
use sp_core::H160;
use evm::{ExitError, ExitSucceed};
use impl_trait_for_tuples::impl_for_tuples;

/// Custom precompiles to be used by EVM engine.
pub trait Precompiles {
	/// Try to execute the code address as precompile. If the code address is not
	/// a precompile or the precompile is not yet available, return `None`.
	/// Otherwise, calculate the amount of gas needed with given `input` and
	/// `target_gas`. Return `Some(Ok(status, output, gas_used))` if the execution
	/// is successful. Otherwise return `Some(Err(_))`.
	fn execute(
		address: H160,
		input: &[u8],
		target_gas: Option<usize>,
	) -> Option<core::result::Result<(ExitSucceed, Vec<u8>, usize), ExitError>>;
}

/// One single precompile used by EVM engine.
pub trait Precompile {
	/// Try to execute the precompile. Calculate the amount of gas needed with given `input` and
	/// `target_gas`. Return `Ok(status, output, gas_used)` if the execution is
	/// successful. Otherwise return `Err(_)`.
	fn execute(
		input: &[u8],
		target_gas: Option<usize>,
	) -> core::result::Result<(ExitSucceed, Vec<u8>, usize), ExitError>;
}

#[impl_for_tuples(16)]
#[tuple_types_no_default_trait_bound]
impl Precompiles for Tuple {
	for_tuples!( where #( Tuple: Precompile )* );

	fn execute(
		address: H160,
		input: &[u8],
		target_gas: Option<usize>,
	) -> Option<core::result::Result<(ExitSucceed, Vec<u8>, usize), ExitError>> {
		let mut index = 0;

		for_tuples!( #(
			index += 1;
			if address == H160::from_low_u64_be(index) {
				return Some(Tuple::execute(input, target_gas))
			}
		)* );

		None
	}
}
