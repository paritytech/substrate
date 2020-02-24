// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! EVM execution module for Substrate

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

mod backend;

pub use crate::backend::{Account, Log, Vicinity, Backend};

use sp_std::{vec::Vec, marker::PhantomData};
use frame_support::{ensure, decl_module, decl_storage, decl_event, decl_error};
use frame_support::weights::{Weight, DispatchClass, FunctionOf};
use frame_support::traits::{Currency, WithdrawReason, ExistenceRequirement};
use frame_system::{self as system, ensure_signed};
use sp_runtime::ModuleId;
use frame_support::weights::SimpleDispatchInfo;
use sp_core::{U256, H256, H160, Hasher};
use sp_runtime::{
	DispatchResult, traits::{UniqueSaturatedInto, AccountIdConversion, SaturatedConversion},
};
use sha3::{Digest, Keccak256};
use evm::{ExitReason, ExitSucceed, ExitError};
use evm::executor::StackExecutor;
use evm::backend::ApplyBackend;

const MODULE_ID: ModuleId = ModuleId(*b"py/ethvm");

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

/// Trait for converting account ids of `balances` module into
/// `H160` for EVM module.
///
/// Accounts and contracts of this module are stored in its own
/// storage, in an Ethereum-compatible format. In order to communicate
/// with the rest of Substrate module, we require an one-to-one
/// mapping of Substrate account to Ethereum address.
pub trait ConvertAccountId<A> {
	/// Given a Substrate address, return the corresponding Ethereum address.
	fn convert_account_id(account_id: &A) -> H160;
}

/// Hash and then truncate the account id, taking the last 160-bit as the Ethereum address.
pub struct HashTruncateConvertAccountId<H>(PhantomData<H>);

impl<H: Hasher> Default for HashTruncateConvertAccountId<H> {
	fn default() -> Self {
		Self(PhantomData)
	}
}

impl<H: Hasher, A: AsRef<[u8]>> ConvertAccountId<A> for HashTruncateConvertAccountId<H> {
	fn convert_account_id(account_id: &A) -> H160 {
		let account_id = H::hash(account_id.as_ref());
		let account_id_len = account_id.as_ref().len();
		let mut value = [0u8; 20];
		let value_len = value.len();

		if value_len > account_id_len {
			value[(value_len - account_id_len)..].copy_from_slice(account_id.as_ref());
		} else {
			value.copy_from_slice(&account_id.as_ref()[(account_id_len - value_len)..]);
		}

		H160::from(value)
	}
}

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
		target_gas: Option<usize>
	) -> Option<core::result::Result<(ExitSucceed, Vec<u8>, usize), ExitError>>;
}

impl Precompiles for () {
	fn execute(
		_address: H160,
		_input: &[u8],
		_target_gas: Option<usize>
	) -> Option<core::result::Result<(ExitSucceed, Vec<u8>, usize), ExitError>> {
		None
	}
}

/// EVM module trait
pub trait Trait: frame_system::Trait + pallet_timestamp::Trait {
	/// Calculator for current gas price.
	type FeeCalculator: FeeCalculator;
	/// Convert account ID to H160;
	type ConvertAccountId: ConvertAccountId<Self::AccountId>;
	/// Currency type for deposit and withdraw.
	type Currency: Currency<Self::AccountId>;
	/// The overarching event type.
	type Event: From<Event> + Into<<Self as frame_system::Trait>::Event>;
	/// Precompiles associated with this EVM engine.
	type Precompiles: Precompiles;
}

decl_storage! {
	trait Store for Module<T: Trait> as Example {
		Accounts get(fn accounts) config(): map hasher(blake2_256) H160 => Account;
		AccountCodes: map hasher(blake2_256) H160 => Vec<u8>;
		AccountStorages: double_map hasher(blake2_256) H160, hasher(blake2_256) H256 => H256;
	}
}

decl_event! {
	/// EVM events
	pub enum Event {
		/// Ethereum events from contracts.
		Log(Log),
		/// A contract has been created at given address.
		Created(H160),
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
		/// Call failed
		ExitReasonFailed,
		/// Call reverted
		ExitReasonRevert,
		/// Call returned VM fatal error
		ExitReasonFatal,
		/// Nonce is invalid
		InvalidNonce,
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		fn deposit_event() = default;

		/// Deposit balance from currency/balances module into EVM.
		#[weight = SimpleDispatchInfo::FixedNormal(10_000)]
		fn deposit_balance(origin, value: BalanceOf<T>) {
			let sender = ensure_signed(origin)?;

			let imbalance = T::Currency::withdraw(
				&sender,
				value,
				WithdrawReason::Reserve.into(),
				ExistenceRequirement::AllowDeath,
			)?;
			T::Currency::resolve_creating(&Self::account_id(), imbalance);

			let bvalue = U256::from(UniqueSaturatedInto::<u128>::unique_saturated_into(value));
			let address = T::ConvertAccountId::convert_account_id(&sender);
			Accounts::mutate(&address, |account| {
				account.balance += bvalue;
			});
		}

		/// Withdraw balance from EVM into currency/balances module.
		#[weight = SimpleDispatchInfo::FixedNormal(10_000)]
		fn withdraw_balance(origin, value: BalanceOf<T>) {
			let sender = ensure_signed(origin)?;
			let address = T::ConvertAccountId::convert_account_id(&sender);
			let bvalue = U256::from(UniqueSaturatedInto::<u128>::unique_saturated_into(value));

			let mut account = Accounts::get(&address);
			account.balance = account.balance.checked_sub(bvalue)
				.ok_or(Error::<T>::BalanceLow)?;

			let imbalance = T::Currency::withdraw(
				&Self::account_id(),
				value,
				WithdrawReason::Reserve.into(),
				ExistenceRequirement::AllowDeath
			)?;

			Accounts::insert(&address, account);

			T::Currency::resolve_creating(&sender, imbalance);
		}

		/// Issue an EVM call operation. This is similar to a message call transaction in Ethereum.
		#[weight = FunctionOf(|(_, _, _, gas_limit, gas_price, _): (&H160, &Vec<u8>, &U256, &u32, &U256, &Option<U256>)| (*gas_price).saturated_into::<Weight>().saturating_mul(*gas_limit), DispatchClass::Normal, true)]
		fn call(
			origin,
			target: H160,
			input: Vec<u8>,
			value: U256,
			gas_limit: u32,
			gas_price: U256,
			nonce: Option<U256>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let source = T::ConvertAccountId::convert_account_id(&sender);

			Self::execute_evm(
				source,
				value,
				gas_limit,
				gas_price,
				nonce,
				|executor| ((), executor.transact_call(
					source,
					target,
					value,
					input,
					gas_limit as usize,
				)),
			).map_err(Into::into)
		}

		/// Issue an EVM create operation. This is similar to a contract creation transaction in
		/// Ethereum.
		#[weight = FunctionOf(|(_, _, gas_limit, gas_price, _): (&Vec<u8>, &U256, &u32, &U256, &Option<U256>)| (*gas_price).saturated_into::<Weight>().saturating_mul(*gas_limit), DispatchClass::Normal, true)]
		fn create(
			origin,
			init: Vec<u8>,
			value: U256,
			gas_limit: u32,
			gas_price: U256,
			nonce: Option<U256>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let source = T::ConvertAccountId::convert_account_id(&sender);

			let create_address = Self::execute_evm(
				source,
				value,
				gas_limit,
				gas_price,
				nonce,
				|executor| {
					(executor.create_address(
						evm::CreateScheme::Legacy { caller: source },
					), executor.transact_create(
						source,
						value,
						init,
						gas_limit as usize,
					))
				},
			)?;

			Module::<T>::deposit_event(Event::Created(create_address));
			Ok(())
		}

		/// Issue an EVM create2 operation.
		#[weight = FunctionOf(|(_, _, _, gas_limit, gas_price, _): (&Vec<u8>, &H256, &U256, &u32, &U256, &Option<U256>)| (*gas_price).saturated_into::<Weight>().saturating_mul(*gas_limit), DispatchClass::Normal, true)]
		fn create2(
			origin,
			init: Vec<u8>,
			salt: H256,
			value: U256,
			gas_limit: u32,
			gas_price: U256,
			nonce: Option<U256>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let source = T::ConvertAccountId::convert_account_id(&sender);

			let code_hash = H256::from_slice(Keccak256::digest(&init).as_slice());
			let create_address = Self::execute_evm(
				source,
				value,
				gas_limit,
				gas_price,
				nonce,
				|executor| {
					(executor.create_address(
						evm::CreateScheme::Create2 { caller: source, code_hash, salt },
					), executor.transact_create2(
						source,
						value,
						init,
						salt,
						gas_limit as usize,
					))
				},
			)?;

			Module::<T>::deposit_event(Event::Created(create_address));
			Ok(())
		}
	}
}

impl<T: Trait> Module<T> {
	/// The account ID of the EVM module.
	///
	/// This actually does computation. If you need to keep using it, then make sure you cache the
	/// value and only call this once.
	pub fn account_id() -> T::AccountId {
		MODULE_ID.into_account()
	}

	/// Check whether an account is empty.
	pub fn is_account_empty(address: &H160) -> bool {
		let account = Accounts::get(address);
		let code_len = AccountCodes::decode_len(address).unwrap_or(0);

		account.nonce == U256::zero() &&
			account.balance == U256::zero() &&
			code_len == 0
	}

	/// Remove an account if its empty.
	pub fn remove_account_if_empty(address: &H160) {
		if Self::is_account_empty(address) {
			Self::remove_account(address)
		}
	}

	/// Remove an account from state.
	fn remove_account(address: &H160) {
		Accounts::remove(address);
		AccountCodes::remove(address);
		AccountStorages::remove_prefix(address);
	}

	/// Execute an EVM operation.
	fn execute_evm<F, R>(
		source: H160,
		value: U256,
		gas_limit: u32,
		gas_price: U256,
		nonce: Option<U256>,
		f: F,
	) -> Result<R, Error<T>> where
		F: FnOnce(&mut StackExecutor<Backend<T>>) -> (R, ExitReason),
	{
		ensure!(gas_price >= T::FeeCalculator::min_gas_price(), Error::<T>::GasPriceTooLow);

		let vicinity = Vicinity {
			gas_price,
			origin: source,
		};

		let mut backend = Backend::<T>::new(&vicinity);
		let mut executor = StackExecutor::new_with_precompile(
			&backend,
			gas_limit as usize,
			&backend::GASOMETER_CONFIG,
			T::Precompiles::execute,
		);

		let total_fee = gas_price.checked_mul(U256::from(gas_limit))
			.ok_or(Error::<T>::FeeOverflow)?;
		let total_payment = value.checked_add(total_fee).ok_or(Error::<T>::PaymentOverflow)?;
		let source_account = Accounts::get(&source);
		ensure!(source_account.balance >= total_payment, Error::<T>::BalanceLow);
		executor.withdraw(source, total_fee).map_err(|_| Error::<T>::WithdrawFailed)?;

		if let Some(nonce) = nonce {
			ensure!(source_account.nonce == nonce, Error::<T>::InvalidNonce);
		}

		let (retv, reason) = f(&mut executor);

		let ret = match reason {
			ExitReason::Succeed(_) => Ok(retv),
			ExitReason::Error(_) => Err(Error::<T>::ExitReasonFailed),
			ExitReason::Revert(_) => Err(Error::<T>::ExitReasonRevert),
			ExitReason::Fatal(_) => Err(Error::<T>::ExitReasonFatal),
		};

		let actual_fee = executor.fee(gas_price);
		executor.deposit(source, total_fee.saturating_sub(actual_fee));

		let (values, logs) = executor.deconstruct();
		backend.apply(values, logs, true);

		ret
	}
}
