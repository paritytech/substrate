// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
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

//! Functions that deal with address derivation.

use crate::{CodeHash, Config};
use codec::{Decode, Encode};
use sp_runtime::traits::{Hash, TrailingZeroInput};

/// Provides the contract address generation method.
///
/// See [`DefaultAddressGenerator`] for the default implementation.
///
/// # Note for implementors
///
/// 1. Make sure that there are no collisions, different inputs never lead to the same output.
/// 2. Make sure that the same inputs lead to the same output.
pub trait AddressGenerator<T: Config> {
	/// The address of a contract based on the given instantiate parameters.
	///
	/// Changing the formular for an already deployed chain is fine as long as no collisons
	/// with the old formular. Changes only affect existing contracts.
	fn contract_address(
		deploying_address: &T::AccountId,
		code_hash: &CodeHash<T>,
		input_data: &[u8],
		salt: &[u8],
	) -> T::AccountId;

	/// The address of the deposit account of `contract_addr`.
	///
	/// The address is generated once on instantiation and then stored in the contracts
	/// metadata. Hence changes do only affect newly created contracts.
	fn deposit_address(contract_addr: &T::AccountId) -> T::AccountId;
}

/// Default address generator.
///
/// This is the default address generator used by contract instantiation. Its result
/// is only dependent on its inputs. It can therefore be used to reliably predict the
/// address of a contract. This is akin to the formula of eth's CREATE2 opcode. There
/// is no CREATE equivalent because CREATE2 is strictly more powerful.
/// Formula:
/// `hash("contract_addr_v1" ++ deploying_address ++ code_hash ++ input_data ++ salt)`
pub struct DefaultAddressGenerator;

impl<T: Config> AddressGenerator<T> for DefaultAddressGenerator {
	/// Formula: `hash("contract_addr_v1" ++ deploying_address ++ code_hash ++ input_data ++ salt)`
	fn contract_address(
		deploying_address: &T::AccountId,
		code_hash: &CodeHash<T>,
		input_data: &[u8],
		salt: &[u8],
	) -> T::AccountId {
		let entropy = (b"contract_addr_v1", deploying_address, code_hash, input_data, salt)
			.using_encoded(T::Hashing::hash);
		Decode::decode(&mut TrailingZeroInput::new(entropy.as_ref()))
			.expect("infinite length input; no invalid inputs for type; qed")
	}

	/// Formula: `hash("contract_depo_v1" ++ contract_addr)`
	fn deposit_address(contract_addr: &T::AccountId) -> T::AccountId {
		let entropy = (b"contract_depo_v1", contract_addr).using_encoded(T::Hashing::hash);
		Decode::decode(&mut TrailingZeroInput::new(entropy.as_ref()))
			.expect("infinite length input; no invalid inputs for type; qed")
	}
}
