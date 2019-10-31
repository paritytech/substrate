// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

extern crate alloc;

mod backend;

pub use crate::backend::{Account, Log, Vicinity, Backend};

use rstd::vec::Vec;
use support::{dispatch::Result, decl_module, decl_storage, decl_event};
use support::traits::{Currency, WithdrawReason, ExistenceRequirement};
use system::ensure_signed;
use sr_primitives::weights::SimpleDispatchInfo;
use sr_primitives::traits::UniqueSaturatedInto;
use primitives::{U256, H256, H160};
use evm::{ExitReason, ExitSucceed, ExitError};
use evm::executor::StackExecutor;
use evm::backend::ApplyBackend;

/// Type alias for currency balance.
pub type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;

/// Trait that outputs the current transaction gas price.
pub trait FeeCalculator {
	/// Return the current gas price.
	fn gas_price() -> U256;
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
	fn convert_account_id(account_id: A) -> H160;
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
pub trait Trait: system::Trait + timestamp::Trait {
	/// Calculator for current gas price.
	type FeeCalculator: FeeCalculator;
	/// Convert account ID to H160;
	type ConvertAccountId: ConvertAccountId<Self::AccountId>;
	/// Currency type for deposit and withdraw.
	type Currency: Currency<Self::AccountId>;
	/// The overarching event type.
	type Event: From<Event> + Into<<Self as system::Trait>::Event>;
	/// Precompiles associated with this EVM engine.
	type Precompiles: Precompiles;
}

decl_storage! {
	trait Store for Module<T: Trait> as Example {
		Accounts get(fn accounts) config(): map H160 => Account;
		AccountStorages: double_map H160, blake2_256(H256) => H256;
	}
}

decl_event!(
	/// EVM events
	pub enum Event {
		/// Ethereum events from contracts.
		Log(Log),
	}
);

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event() = default;

		#[weight = SimpleDispatchInfo::FixedNormal(10_000)]
		fn deposit_balance(origin, value: BalanceOf<T>) -> Result {
			let sender = ensure_signed(origin)?;

			T::Currency::withdraw(
				&sender,
				value,
				WithdrawReason::Reserve.into(),
				ExistenceRequirement::KeepAlive,
			)?;

			let bvalue = U256::from(UniqueSaturatedInto::<u64>::unique_saturated_into(value));
			let address = T::ConvertAccountId::convert_account_id(sender);
			Accounts::mutate(&address, |account| {
				account.balance += bvalue;
			});

			Ok(())
		}

		#[weight = SimpleDispatchInfo::FixedNormal(10_000)]
		fn withdraw_balance(origin, value: BalanceOf<T>) -> Result {
			let sender = ensure_signed(origin)?;
			let address = T::ConvertAccountId::convert_account_id(sender.clone());
			let bvalue = U256::from(UniqueSaturatedInto::<u64>::unique_saturated_into(value));

			if Accounts::get(&address).balance < bvalue {
				return Err("Not enough balance to withdraw")
			}

			Accounts::mutate(&address, |account| {
				account.balance -= bvalue;
			});

			T::Currency::deposit_creating(&sender, value);

			Ok(())
		}

		#[weight = SimpleDispatchInfo::FixedNormal(10_000)]
		fn call(origin, target: H160, input: Vec<u8>, value: U256, gas_limit: u32) -> Result {
			let sender = ensure_signed(origin)?;
			let source = T::ConvertAccountId::convert_account_id(sender.clone());
			let gas_price = T::FeeCalculator::gas_price();

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

			let total_fee = gas_price * U256::from(gas_limit);
			if Accounts::get(&source).balance < value + total_fee {
				return Err("Not enough balance to pay transaction fee")
			}
			executor.withdraw(source, total_fee).map_err(|_| "Withdraw fee failed")?;

			let reason = executor.transact_call(
				source,
				target,
				value,
				input,
				gas_limit as usize,
			);

			let ret = match reason {
				ExitReason::Succeed(_) => Ok(()),
				_ => Err("Execute message call failed")
			};
			let actual_fee = executor.fee(gas_price);
			executor.deposit(source, total_fee - actual_fee);

			let (values, logs) = executor.deconstruct();
			backend.apply(values, logs, true);

			ret
		}

		#[weight = SimpleDispatchInfo::FixedNormal(10_000)]
		fn create(origin, init: Vec<u8>, value: U256, gas_limit: u32) -> Result {
			let sender = ensure_signed(origin)?;
			let source = T::ConvertAccountId::convert_account_id(sender.clone());
			let gas_price = T::FeeCalculator::gas_price();

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

			let total_fee = gas_price * U256::from(gas_limit);
			if Accounts::get(&source).balance < value + total_fee {
				return Err("Not enough balance to pay transaction fee")
			}
			executor.withdraw(source, total_fee).map_err(|_| "Withdraw fee failed")?;

			let reason = executor.transact_create(
				source,
				value,
				init,
				gas_limit as usize,
			);

			let ret = match reason {
				ExitReason::Succeed(_) => Ok(()),
				_ => Err("Execute message call failed")
			};
			let actual_fee = executor.fee(gas_price);
			executor.deposit(source, total_fee - actual_fee);

			let (values, logs) = executor.deconstruct();
			backend.apply(values, logs, true);

			ret
		}
	}
}
