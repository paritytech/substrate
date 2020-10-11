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

pub mod stack;
pub mod native;

use sp_std::vec::Vec;
#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
use codec::{Encode, Decode};
use sp_core::{H160, U256, H256};
use evm::ExitReason;
use crate::Trait;

#[derive(Clone, Eq, PartialEq, Encode, Decode, Default)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
/// Ethereum account nonce, balance and code. Used by storage.
pub struct Account {
	/// Account nonce.
	pub nonce: U256,
	/// Account balance.
	pub balance: U256,
}

#[derive(Clone, Eq, PartialEq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
/// Ethereum log. Used for `deposit_event`.
pub struct Log {
	/// Source address of the log.
	pub address: H160,
	/// Topics of the log.
	pub topics: Vec<H256>,
	/// Byte array data of the log.
	pub data: Vec<u8>,
}

#[derive(Clone, Eq, PartialEq, Encode, Decode, Default)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
/// External input from the transaction.
pub struct Vicinity {
	/// Current transaction gas price.
	pub gas_price: U256,
	/// Origin of the transaction.
	pub origin: H160,
}

pub struct ExecutionInfo<T> {
	pub exit_reason: ExitReason,
	pub value: T,
}

pub type CallInfo = ExecutionInfo<Vec<u8>>;
pub type CreateInfo = ExecutionInfo<H160>;

pub trait Runner<T: Trait> {
	type Error: Into<sp_runtime::DispatchError>;

	fn call(
		source: H160,
		target: H160,
		input: Vec<u8>,
		value: U256,
		gas_limit: u32,
		gas_price: U256,
		nonce: Option<U256>,
	) -> Result<CallInfo, Self::Error>;

	fn create(
		source: H160,
		init: Vec<u8>,
		value: U256,
		gas_limit: u32,
		gas_price: U256,
		nonce: Option<U256>,
	) -> Result<CreateInfo, Self::Error>;

	fn create2(
		source: H160,
		init: Vec<u8>,
		salt: H256,
		value: U256,
		gas_limit: u32,
		gas_price: U256,
		nonce: Option<U256>,
	) -> Result<CreateInfo, Self::Error>;
}
