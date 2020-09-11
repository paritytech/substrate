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

//! Builtin precompiles.

use sp_std::{cmp::min, vec::Vec};
use sp_core::H160;
use evm::{ExitError, ExitSucceed};
use ripemd160::Digest;
use impl_trait_for_tuples::impl_for_tuples;
use eth_pairings::public_interface::eip2537::{EIP2537Executor};

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

/// Linear gas cost
fn ensure_linear_cost(
	target_gas: Option<usize>,
	len: usize,
	base: usize,
	word: usize
) -> Result<usize, ExitError> {
	let cost = base.checked_add(
		word.checked_mul(len.saturating_add(31) / 32).ok_or(ExitError::OutOfGas)?
	).ok_or(ExitError::OutOfGas)?;

	if let Some(target_gas) = target_gas {
		if cost > target_gas {
			return Err(ExitError::OutOfGas)
		}
	}

	Ok(cost)
}

/// The identity precompile.
pub struct Identity;

impl Precompile for Identity {
	fn execute(
		input: &[u8],
		target_gas: Option<usize>,
	) -> core::result::Result<(ExitSucceed, Vec<u8>, usize), ExitError> {
		let cost = ensure_linear_cost(target_gas, input.len(), 15, 3)?;

		Ok((ExitSucceed::Returned, input.to_vec(), cost))
	}
}

/// The ecrecover precompile.
pub struct ECRecover;

impl Precompile for ECRecover {
	fn execute(
		i: &[u8],
		target_gas: Option<usize>,
	) -> core::result::Result<(ExitSucceed, Vec<u8>, usize), ExitError> {
		let cost = ensure_linear_cost(target_gas, i.len(), 3000, 0)?;

		let mut input = [0u8; 128];
		input[..min(i.len(), 128)].copy_from_slice(&i[..min(i.len(), 128)]);

		let mut msg = [0u8; 32];
		let mut sig = [0u8; 65];

		msg[0..32].copy_from_slice(&input[0..32]);
		sig[0..32].copy_from_slice(&input[64..96]);
		sig[32..64].copy_from_slice(&input[96..128]);
		sig[64] = input[63];

		let pubkey = sp_io::crypto::secp256k1_ecdsa_recover(&sig, &msg)
			.map_err(|_| ExitError::Other("Public key recover failed"))?;
		let mut address = sp_io::hashing::keccak_256(&pubkey);
		address[0..12].copy_from_slice(&[0u8; 12]);

		Ok((ExitSucceed::Returned, address.to_vec(), cost))
	}
}

/// The ripemd precompile.
pub struct Ripemd160;

impl Precompile for Ripemd160 {
	fn execute(
		input: &[u8],
		target_gas: Option<usize>,
	) -> core::result::Result<(ExitSucceed, Vec<u8>, usize), ExitError> {
		let cost = ensure_linear_cost(target_gas, input.len(), 600, 120)?;

		let ret = ripemd160::Ripemd160::digest(input).to_vec();
		Ok((ExitSucceed::Returned, ret, cost))
	}
}

/// The sha256 precompile.
pub struct Sha256;

impl Precompile for Sha256 {
	fn execute(
		input: &[u8],
		target_gas: Option<usize>,
	) -> core::result::Result<(ExitSucceed, Vec<u8>, usize), ExitError> {
		let cost = ensure_linear_cost(target_gas, input.len(), 60, 12)?;

		let ret = sp_io::hashing::sha2_256(input);
		Ok((ExitSucceed::Returned, ret.to_vec(), cost))
	}
}

/// The Bls12G1Add builtin.
pub struct Bls12G1Add;

/// The Bls12G1Mul builtin.
pub struct Bls12G1Mul;

/// The Bls12G1MultiExp builtin.
pub struct Bls12G1MultiExp;

/// The Bls12G2Add builtin.
pub struct Bls12G2Add;

/// The Bls12G2Mul builtin.
pub struct Bls12G2Mul;

/// The Bls12G2MultiExp builtin.
pub struct Bls12G2MultiExp;

/// The Bls12Pairing builtin.
pub struct Bls12Pairing;

/// The Bls12MapFpToG1 builtin.
pub struct Bls12MapFpToG1;

/// The Bls12MapFp2ToG2 builtin.
pub struct Bls12MapFp2ToG2;

impl Precompile for Bls12G1Add {
	fn execute(
		input: &[u8],
		target_gas: Option<usize>,
	) -> core::result::Result<(ExitSucceed, Vec<u8>, usize), ExitError> {
		let cost = ensure_linear_cost(target_gas, input.len(), 15, 3)?;

		let result = EIP2537Executor::g1_add(input);

		match result {
			Ok(result_bytes) => {
				Ok((ExitSucceed::Returned, result_bytes.to_vec(), cost))
			},
			Err(_e) => {
				Err(ExitError::Other("Bls12G1Add error"))
			}
		}
		
	}
}

impl Precompile for Bls12G1Mul {
	fn execute(
		input: &[u8],
		target_gas: Option<usize>,
	) -> core::result::Result<(ExitSucceed, Vec<u8>, usize), ExitError> {
		let cost = ensure_linear_cost(target_gas, input.len(), 15, 3)?;

		let result = EIP2537Executor::g1_mul(input);

		match result {
			Ok(result_bytes) => {
				Ok((ExitSucceed::Returned, result_bytes.to_vec(), cost))
			},
			Err(_e) => {
				Err(ExitError::Other("Bls12G1Mul error"))
			}
		}
	}
}

impl Precompile for Bls12G1MultiExp {
	fn execute(
		input: &[u8],
		target_gas: Option<usize>,
	) -> core::result::Result<(ExitSucceed, Vec<u8>, usize), ExitError> {
		let cost = ensure_linear_cost(target_gas, input.len(), 15, 3)?;

		let result = EIP2537Executor::g1_multiexp(input);

		match result {
			Ok(result_bytes) => {
				Ok((ExitSucceed::Returned, result_bytes.to_vec(), cost))
			},
			Err(_e) => {
				Err(ExitError::Other("Bls12G1MultiExp error"))
			}
		}
	}
}

impl Precompile for Bls12G2Add {
	fn execute(
		input: &[u8],
		target_gas: Option<usize>,
	) -> core::result::Result<(ExitSucceed, Vec<u8>, usize), ExitError> {
		let cost = ensure_linear_cost(target_gas, input.len(), 15, 3)?;

		let result = EIP2537Executor::g2_add(input);

		match result {
			Ok(result_bytes) => {
				Ok((ExitSucceed::Returned, result_bytes.to_vec(), cost))
			},
			Err(_e) => {
				Err(ExitError::Other("Bls12G2Add error"))
			}
		}
	}
}

impl Precompile for Bls12G2Mul {
	fn execute(
		input: &[u8],
		target_gas: Option<usize>,
	) -> core::result::Result<(ExitSucceed, Vec<u8>, usize), ExitError> {
		let cost = ensure_linear_cost(target_gas, input.len(), 15, 3)?;

		let result = EIP2537Executor::g2_mul(input);

		match result {
			Ok(result_bytes) => {
				Ok((ExitSucceed::Returned, result_bytes.to_vec(), cost))
			},
			Err(_e) => {
				Err(ExitError::Other("Bls12G2Mul error"))
			}
		}
	}
}

impl Precompile for Bls12G2MultiExp {
	fn execute(
		input: &[u8],
		target_gas: Option<usize>,
	) -> core::result::Result<(ExitSucceed, Vec<u8>, usize), ExitError> {
		let cost = ensure_linear_cost(target_gas, input.len(), 15, 3)?;

		let result = EIP2537Executor::g2_multiexp(input);

		match result {
			Ok(result_bytes) => {
				Ok((ExitSucceed::Returned, result_bytes.to_vec(), cost))
			},
			Err(_e) => {
				Err(ExitError::Other("Bls12G2MultiExp error"))
			}
		}
	}
}

impl Precompile for Bls12Pairing {
	fn execute(
		input: &[u8],
		target_gas: Option<usize>,
	) -> core::result::Result<(ExitSucceed, Vec<u8>, usize), ExitError> {
		let cost = ensure_linear_cost(target_gas, input.len(), 15, 3)?;

		let result = EIP2537Executor::pair(input);

		match result {
			Ok(result_bytes) => {
				Ok((ExitSucceed::Returned, result_bytes.to_vec(), cost))
			},
			Err(_e) => {
				Err(ExitError::Other("Bls12Pairing error"))
			}
		}
	}
}

impl Precompile for Bls12MapFpToG1 {
	fn execute(
		input: &[u8],
		target_gas: Option<usize>,
	) -> core::result::Result<(ExitSucceed, Vec<u8>, usize), ExitError> {
		let cost = ensure_linear_cost(target_gas, input.len(), 15, 3)?;

		let result = EIP2537Executor::map_fp_to_g1(input);

		match result {
			Ok(result_bytes) => {
				Ok((ExitSucceed::Returned, result_bytes.to_vec(), cost))
			},
			Err(_e) => {
				Err(ExitError::Other("Bls12MapFpToG1 error"))
			}
		}
	}
}

impl Precompile for Bls12MapFp2ToG2 {
	fn execute(
		input: &[u8],
		target_gas: Option<usize>,
	) -> core::result::Result<(ExitSucceed, Vec<u8>, usize), ExitError> {
		let cost = ensure_linear_cost(target_gas, input.len(), 15, 3)?;

		let result = EIP2537Executor::map_fp2_to_g2(input);

		match result {
			Ok(result_bytes) => {
				Ok((ExitSucceed::Returned, result_bytes.to_vec(), cost))
			},
			Err(_e) => {
				Err(ExitError::Other("Bls12MapFp2ToG2 error"))
			}
		}
	}
}