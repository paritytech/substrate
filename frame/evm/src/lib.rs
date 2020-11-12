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

//! # EVM Module
//!
//! The EVM module allows unmodified EVM code to be executed in a Substrate-based blockchain.
//! - [`evm::Trait`]
//!
//! ## EVM Engine
//!
//! The EVM module uses [`SputnikVM`](https://github.com/rust-blockchain/evm) as the underlying EVM engine.
//! The engine is overhauled so that it's [`modular`](https://github.com/corepaper/evm).
//!
//! ## Execution Lifecycle
//!
//! There are a separate set of accounts managed by the EVM module. Substrate based accounts can call the EVM Module
//! to deposit or withdraw balance from the Substrate base-currency into a different balance managed and used by
//! the EVM module. Once a user has populated their balance, they can create and call smart contracts using this module.
//!
//! There's one-to-one mapping from Substrate accounts and EVM external accounts that is defined by a conversion function.
//!
//! ## EVM Module vs Ethereum Network
//!
//! The EVM module should be able to produce nearly identical results compared to the Ethereum mainnet,
//! including gas cost and balance changes.
//!
//! Observable differences include:
//!
//! - The available length of block hashes may not be 256 depending on the configuration of the System module
//! in the Substrate runtime.
//! - Difficulty and coinbase, which do not make sense in this module and is currently hard coded to zero.
//!
//! We currently do not aim to make unobservable behaviors, such as state root, to be the same. We also don't aim to follow
//! the exact same transaction / receipt format. However, given one Ethereum transaction and one Substrate account's
//! private key, one should be able to convert any Ethereum transaction into a transaction compatible with this module.
//!
//! The gas configurations are configurable. Right now, a pre-defined Istanbul hard fork configuration option is provided.

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

mod tests;
pub mod runner;
pub mod precompiles;

pub use crate::precompiles::{Precompile, Precompiles};
pub use crate::runner::Runner;
pub use sp_evm::{Account, Log, Vicinity, ExecutionInfo, CallInfo, CreateInfo};
pub use evm::{ExitReason, ExitSucceed, ExitError, ExitRevert, ExitFatal};

use sp_std::vec::Vec;
#[cfg(feature = "std")]
use codec::{Encode, Decode};
#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
use frame_support::{decl_module, decl_storage, decl_event, decl_error};
use frame_support::weights::{Weight, Pays};
use frame_support::traits::{Currency, ExistenceRequirement, Get};
use frame_support::dispatch::DispatchResultWithPostInfo;
use frame_system::RawOrigin;
use sp_core::{U256, H256, H160, Hasher};
use sp_runtime::{AccountId32, traits::{UniqueSaturatedInto, SaturatedConversion, BadOrigin}};
use evm::Config;

/// Type alias for currency balance.
pub type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

/// Trait that outputs the current transaction gas price.
pub trait FeeCalculator {
	/// Return the minimal required gas price.
	fn min_gas_price() -> U256;
}

impl FeeCalculator for () {
	fn min_gas_price() -> U256 { U256::zero() }
}

pub trait EnsureAddressOrigin<OuterOrigin> {
	/// Success return type.
	type Success;

	/// Perform the origin check.
	fn ensure_address_origin(
		address: &H160,
		origin: OuterOrigin,
	) -> Result<Self::Success, BadOrigin> {
		Self::try_address_origin(address, origin).map_err(|_| BadOrigin)
	}

	/// Try with origin.
	fn try_address_origin(
		address: &H160,
		origin: OuterOrigin,
	) -> Result<Self::Success, OuterOrigin>;
}

/// Ensure that the EVM address is the same as the Substrate address. This only works if the account
/// ID is `H160`.
pub struct EnsureAddressSame;

impl<OuterOrigin> EnsureAddressOrigin<OuterOrigin> for EnsureAddressSame where
	OuterOrigin: Into<Result<RawOrigin<H160>, OuterOrigin>> + From<RawOrigin<H160>>,
{
	type Success = H160;

	fn try_address_origin(
		address: &H160,
		origin: OuterOrigin,
	) -> Result<H160, OuterOrigin> {
		origin.into().and_then(|o| match o {
			RawOrigin::Signed(who) if &who == address => Ok(who),
			r => Err(OuterOrigin::from(r))
		})
	}
}

/// Ensure that the origin is root.
pub struct EnsureAddressRoot<AccountId>(sp_std::marker::PhantomData<AccountId>);

impl<OuterOrigin, AccountId> EnsureAddressOrigin<OuterOrigin> for EnsureAddressRoot<AccountId> where
	OuterOrigin: Into<Result<RawOrigin<AccountId>, OuterOrigin>> + From<RawOrigin<AccountId>>,
{
	type Success = ();

	fn try_address_origin(
		_address: &H160,
		origin: OuterOrigin,
	) -> Result<(), OuterOrigin> {
		origin.into().and_then(|o| match o {
			RawOrigin::Root => Ok(()),
			r => Err(OuterOrigin::from(r)),
		})
	}
}

/// Ensure that the origin never happens.
pub struct EnsureAddressNever<AccountId>(sp_std::marker::PhantomData<AccountId>);

impl<OuterOrigin, AccountId> EnsureAddressOrigin<OuterOrigin> for EnsureAddressNever<AccountId> {
	type Success = AccountId;

	fn try_address_origin(
		_address: &H160,
		origin: OuterOrigin,
	) -> Result<AccountId, OuterOrigin> {
		Err(origin)
	}
}

/// Ensure that the address is truncated hash of the origin. Only works if the account id is
/// `AccountId32`.
pub struct EnsureAddressTruncated;

impl<OuterOrigin> EnsureAddressOrigin<OuterOrigin> for EnsureAddressTruncated where
	OuterOrigin: Into<Result<RawOrigin<AccountId32>, OuterOrigin>> + From<RawOrigin<AccountId32>>,
{
	type Success = AccountId32;

	fn try_address_origin(
		address: &H160,
		origin: OuterOrigin,
	) -> Result<AccountId32, OuterOrigin> {
		origin.into().and_then(|o| match o {
			RawOrigin::Signed(who)
				if AsRef::<[u8; 32]>::as_ref(&who)[0..20] == address[0..20] => Ok(who),
			r => Err(OuterOrigin::from(r))
		})
	}
}

pub trait AddressMapping<A> {
	fn into_account_id(address: H160) -> A;
}

/// Identity address mapping.
pub struct IdentityAddressMapping;

impl AddressMapping<H160> for IdentityAddressMapping {
	fn into_account_id(address: H160) -> H160 { address }
}

/// Hashed address mapping.
pub struct HashedAddressMapping<H>(sp_std::marker::PhantomData<H>);

impl<H: Hasher<Out=H256>> AddressMapping<AccountId32> for HashedAddressMapping<H> {
	fn into_account_id(address: H160) -> AccountId32 {
		let mut data = [0u8; 24];
		data[0..4].copy_from_slice(b"evm:");
		data[4..24].copy_from_slice(&address[..]);
		let hash = H::hash(&data);

		AccountId32::from(Into::<[u8; 32]>::into(hash))
	}
}

/// Substrate system chain ID.
pub struct SystemChainId;

impl Get<u64> for SystemChainId {
	fn get() -> u64 {
		sp_io::misc::chain_id()
	}
}

static ISTANBUL_CONFIG: Config = Config::istanbul();

/// EVM module trait
pub trait Trait: frame_system::Trait + pallet_timestamp::Trait {
	/// Calculator for current gas price.
	type FeeCalculator: FeeCalculator;

	/// Allow the origin to call on behalf of given address.
	type CallOrigin: EnsureAddressOrigin<Self::Origin>;
	/// Allow the origin to withdraw on behalf of given address.
	type WithdrawOrigin: EnsureAddressOrigin<Self::Origin, Success=Self::AccountId>;

	/// Mapping from address to account id.
	type AddressMapping: AddressMapping<Self::AccountId>;
	/// Currency type for withdraw and balance storage.
	type Currency: Currency<Self::AccountId>;

	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
	/// Precompiles associated with this EVM engine.
	type Precompiles: Precompiles;
	/// Chain ID of EVM.
	type ChainId: Get<u64>;
	/// EVM execution runner.
	type Runner: Runner<Self>;

	/// EVM config used in the module.
	fn config() -> &'static Config {
		&ISTANBUL_CONFIG
	}
}

#[cfg(feature = "std")]
#[derive(Clone, Eq, PartialEq, Encode, Decode, Debug, Serialize, Deserialize)]
/// Account definition used for genesis block construction.
pub struct GenesisAccount {
	/// Account nonce.
	pub nonce: U256,
	/// Account balance.
	pub balance: U256,
	/// Full account storage.
	pub storage: std::collections::BTreeMap<H256, H256>,
	/// Account code.
	pub code: Vec<u8>,
}

decl_storage! {
	trait Store for Module<T: Trait> as EVM {
		AccountCodes get(fn account_codes): map hasher(blake2_128_concat) H160 => Vec<u8>;
		AccountStorages get(fn account_storages):
			double_map hasher(blake2_128_concat) H160, hasher(blake2_128_concat) H256 => H256;
	}

	add_extra_genesis {
		config(accounts): std::collections::BTreeMap<H160, GenesisAccount>;
		build(|config: &GenesisConfig| {
			for (address, account) in &config.accounts {
				let account_id = T::AddressMapping::into_account_id(*address);

				// ASSUME: in one single EVM transaction, the nonce will not increase more than
				// `u128::max_value()`.
				for _ in 0..account.nonce.low_u128() {
					frame_system::Module::<T>::inc_account_nonce(&account_id);
				}

				T::Currency::deposit_creating(
					&account_id,
					account.balance.low_u128().unique_saturated_into(),
				);

				AccountCodes::insert(address, &account.code);

				for (index, value) in &account.storage {
					AccountStorages::insert(address, index, value);
				}
			}
		});
	}
}

decl_event! {
	/// EVM events
	pub enum Event<T> where
		<T as frame_system::Trait>::AccountId,
	{
		/// Ethereum events from contracts.
		Log(Log),
		/// A contract has been created at given \[address\].
		Created(H160),
		/// A \[contract\] was attempted to be created, but the execution failed.
		CreatedFailed(H160),
		/// A \[contract\] has been executed successfully with states applied.
		Executed(H160),
		/// A \[contract\] has been executed with errors. States are reverted with only gas fees applied.
		ExecutedFailed(H160),
		/// A deposit has been made at a given address. \[sender, address, value\]
		BalanceDeposit(AccountId, H160, U256),
		/// A withdrawal has been made from a given address. \[sender, address, value\]
		BalanceWithdraw(AccountId, H160, U256),
	}
}

decl_error! {
	pub enum Error for Module<T: Trait> {
		/// Not enough balance to perform action
		BalanceLow,
		/// Calculating total fee overflowed
		FeeOverflow,
		/// Calculating total payment overflowed
		PaymentOverflow,
		/// Withdraw fee failed
		WithdrawFailed,
		/// Gas price is too low.
		GasPriceTooLow,
		/// Nonce is invalid
		InvalidNonce,
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		fn deposit_event() = default;

		/// Withdraw balance from EVM into currency/balances module.
		#[weight = 0]
		fn withdraw(origin, address: H160, value: BalanceOf<T>) {
			let destination = T::WithdrawOrigin::ensure_address_origin(&address, origin)?;
			let address_account_id = T::AddressMapping::into_account_id(address);

			T::Currency::transfer(
				&address_account_id,
				&destination,
				value,
				ExistenceRequirement::AllowDeath
			)?;
		}

		/// Issue an EVM call operation. This is similar to a message call transaction in Ethereum.
		#[weight = (*gas_price).saturated_into::<Weight>().saturating_mul(*gas_limit as Weight)]
		fn call(
			origin,
			source: H160,
			target: H160,
			input: Vec<u8>,
			value: U256,
			gas_limit: u32,
			gas_price: U256,
			nonce: Option<U256>,
		) -> DispatchResultWithPostInfo {
			T::CallOrigin::ensure_address_origin(&source, origin)?;

			match T::Runner::call(
				source,
				target,
				input,
				value,
				gas_limit,
				Some(gas_price),
				nonce,
			)? {
				CallInfo {
					exit_reason: ExitReason::Succeed(_),
					..
				} => {
					Module::<T>::deposit_event(Event::<T>::Executed(target));
				},
				_ => {
					Module::<T>::deposit_event(Event::<T>::ExecutedFailed(target));
				},
			}

			Ok(Pays::No.into())
		}

		/// Issue an EVM create operation. This is similar to a contract creation transaction in
		/// Ethereum.
		#[weight = (*gas_price).saturated_into::<Weight>().saturating_mul(*gas_limit as Weight)]
		fn create(
			origin,
			source: H160,
			init: Vec<u8>,
			value: U256,
			gas_limit: u32,
			gas_price: U256,
			nonce: Option<U256>,
		) -> DispatchResultWithPostInfo {
			T::CallOrigin::ensure_address_origin(&source, origin)?;

			match T::Runner::create(
				source,
				init,
				value,
				gas_limit,
				Some(gas_price),
				nonce,
			)? {
				CreateInfo {
					exit_reason: ExitReason::Succeed(_),
					value: create_address,
					..
				} => {
					Module::<T>::deposit_event(Event::<T>::Created(create_address));
				},
				CreateInfo {
					exit_reason: _,
					value: create_address,
					..
				} => {
					Module::<T>::deposit_event(Event::<T>::CreatedFailed(create_address));
				},
			}

			Ok(Pays::No.into())
		}

		/// Issue an EVM create2 operation.
		#[weight = (*gas_price).saturated_into::<Weight>().saturating_mul(*gas_limit as Weight)]
		fn create2(
			origin,
			source: H160,
			init: Vec<u8>,
			salt: H256,
			value: U256,
			gas_limit: u32,
			gas_price: U256,
			nonce: Option<U256>,
		) -> DispatchResultWithPostInfo {
			T::CallOrigin::ensure_address_origin(&source, origin)?;

			match T::Runner::create2(
				source,
				init,
				salt,
				value,
				gas_limit,
				Some(gas_price),
				nonce,
			)? {
				CreateInfo {
					exit_reason: ExitReason::Succeed(_),
					value: create_address,
					..
				} => {
					Module::<T>::deposit_event(Event::<T>::Created(create_address));
				},
				CreateInfo {
					exit_reason: _,
					value: create_address,
					..
				} => {
					Module::<T>::deposit_event(Event::<T>::CreatedFailed(create_address));
				},
			}

			Ok(Pays::No.into())
		}
	}
}

impl<T: Trait> Module<T> {
	/// Check whether an account is empty.
	pub fn is_account_empty(address: &H160) -> bool {
		let account = Self::account_basic(address);
		let code_len = AccountCodes::decode_len(address).unwrap_or(0);

		account.nonce == U256::zero() &&
			account.balance == U256::zero() &&
			code_len == 0
	}

	/// Remove an account if its empty.
	pub fn remove_account_if_empty(address: &H160) {
		if Self::is_account_empty(address) {
			Self::remove_account(address);
		}
	}

	/// Remove an account.
	pub fn remove_account(address: &H160) {
		AccountCodes::remove(address);
		AccountStorages::remove_prefix(address);
	}

	/// Get the account basic in EVM format.
	pub fn account_basic(address: &H160) -> Account {
		let account_id = T::AddressMapping::into_account_id(*address);

		let nonce = frame_system::Module::<T>::account_nonce(&account_id);
		let balance = T::Currency::free_balance(&account_id);

		Account {
			nonce: U256::from(UniqueSaturatedInto::<u128>::unique_saturated_into(nonce)),
			balance: U256::from(UniqueSaturatedInto::<u128>::unique_saturated_into(balance)),
		}
	}
}
