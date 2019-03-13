// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! ## Overview
//! 
//! The `fees` module handles transaction fee related operations. To use this module, the [`TransferAsset`](https://crates.parity.io/srml_fees/trait.Trait.html#associatedtype.TransferAsset) trait must be implemented to enable asset transfer between accounts. This module provides the following functionality
//! 
//! - Getting and setting the base and per-byte transaction fee
//! - Tracking the overall charged fees for each transaction
//! - Charging and refunding transaction fees
//! 
//! ## Interface
//! 
//! ### Dispatchable
//! 
//! This module is intended to be called by other modules rather than transactions (no dispatchable functions).
//! 
//! ### Public
//! 
//! The following methods are publicly accessible to other modules that implement the [`ChargeFee`](https://github.com/paritytech/substrate/blob/master/srml/fees/src/lib.rs#L93) trait.
//! 
//! - [`charge_fee`](https://github.com/paritytech/substrate/blob/master/srml/fees/src/lib.rs#L96) - handles subtracting transaction fees from the transactor's account
//! - [`refund_fee`](https://github.com/paritytech/substrate/blob/master/srml/fees/src/lib.rs#L107) - handles transaction fee refunds to the transactor's account
//! 
//! ## Usage
//! 
//! ### Prerequisites
//! 
//! The fees module depends on the [`system`](https://crates.parity.io/srml_system/index.html) and [`support`](https://crates.parity.io/srml_support/index.html) modules as well as Substrate Core libraries and the Rust standard library.
//! 
//! ### Simple Code Snippet
//! 
//! Use the `ChargeFee` trait to charge and refund fees.
//! 
//! ```rust,ignore
//! T::ChargeFee::charge_fee(transactor, fee);
//! T::ChargeFee::refund_fee(transactor, fee);
//! ```
//! 
//! ### Example from SRML
//! 
//! The `ChargeFee` trait is invoked in the `balances` and `contract` modules to manage fee-related logic in the following ways
//! 1. `balances`: transfer/creation fee
//! 2. `contract`: gas fee refund/buy
//! 
//! [In the balances module](https://github.com/paritytech/substrate/blob/687cf01ed34ee12d7aaf49bf99d7276192bc8363/srml/balances/src/lib.rs#L58), the `ChargeFee` trait is imported in the module's configuration trait:
//! ```rust,ignore
//! type ChargeFee: ChargeFee<Self::AccountId, Amount=Self::Balance>;
//! ```
//! 
//! It is [later](https://github.com/paritytech/substrate/blob/687cf01ed34ee12d7aaf49bf99d7276192bc8363/srml/balances/src/lib.rs#L328) utilized to charge a transaction fee when the `transactor != dest` (any transfer betweeen different accounts):
//! ```rust,ignore
//! if transactor != dest {
//!     T::ChargeFee::charge_fee(transactor, fee)?;
//!     ...
//! }
//! ```
//! 
//! In the `contract` module, the `ChargeFee` trait is used to refund the gas fee ([ex](https://github.com/paritytech/substrate/pull/1815/files#diff-2179e1ee855613aa8f3343cf87154fe4R241)):
//! ```rust,ignore
//! let _ = <T as Trait>::ChargeFee::refund_fee(transactor, refund);
//! ```
//! 
//! Moreover the following code in [substrate/node/runtime/src/lib.rs](https://github.com/paritytech/substrate/blob/687cf01ed34ee12d7aaf49bf99d7276192bc8363/node/runtime/src/lib.rs#L106) hooks the `fees` module and `balances` module, thereby enabling greater flexibility when implementing and extending the `ChargeFee` trait.
//! ```rust,ignore
//! impl balances::Trait for Runtime {
//! 	type Balance = Balance;
//! 	type OnFreeBalanceZero = ((Staking, Contract), Session);
//! 	type OnNewAccount = Indices;
//! 	type ChargeFee = fees::Module<Runtime>;
//! 	type Event = Event;
//! }
//! ```
//! 
//! A [similar configuration](https://github.com/paritytech/substrate/blob/6ac1f183e0852a387953592d31f01957ff3c76f8/node/runtime/src/lib.rs#L111) involves utilizing the `balances` module in the `fees` implementation.
//! ```rust,ignore
//! impl fees::Trait for Runtime {
//! 	type Event = Event;
//! 	type TransferAsset = Balances;
//! }
//! ```
//! If a chain does not have the `balances` module, then `TransferAsset` can be set to `()`
//! ```rust,ignore
//! type TransferAsset = ();
//! ```
//! In this case, no fee will be charged. Therefore, chains with different implementations of the balances module only need to implement the `TransferAsset` trait in order to be used by the `fees` module.
//! 
//! <!-- ([ongoing PR](https://github.com/paritytech/substrate/issues/1923)) In addition, it is possible to provide `fees` information to other modules. With this functionality, modules can more easily manage accumulated fees within the current block.
//! ```rust,ignore
//! pub trait OnFeeCharged<Amount> {
//! 	fn on_fee_charged(fee: &Amount);
//! }
//! ```
//! This functionality provides greater flexibility when distributing fees to validators (and other relevant actors). -->
//! 
//! ## Genesis Config
//! 
//! Configuration is in `<your-node-name>/src/chain_spec.rs`. The following storage items are configurable:
//! 
//! - `transaction_base_fee`
//! - `transaction_byte_fee`
//! 
//! ## Related Modules
//! 
//! - [**Balances**](https://crates.parity.io/srml_balances/index.html): used for the implementation of the `TransferAsset` trait to be used by the `fees` module
//! - [**Session**](https://crates.parity.io/srml_session/index.html): provides context for the accumulation of fees (throughout a session)
//! - [**System**](https://crates.parity.io/srml_system/index.html): used to obtain block number and time, among other details
//! 
//! ## References
//! 
//! There are no references at this time. <!-- expect to add references to state rent implementations-->

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use srml_support::{
	dispatch::Result, StorageMap, decl_event, decl_storage, decl_module,
	traits::{ArithmeticType, ChargeBytesFee, ChargeFee, TransferAsset, WithdrawReason}
};
use runtime_primitives::traits::{
	As, CheckedAdd, CheckedSub, CheckedMul, Zero
};
use system;

mod mock;
mod tests;

type AssetOf<T> = <<T as Trait>::TransferAsset as ArithmeticType>::Type;

pub trait Trait: system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	/// A function does the asset transfer between accounts
	type TransferAsset: ArithmeticType + TransferAsset<Self::AccountId, Amount=AssetOf<Self>>;
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event<T>() = default;

		fn on_finalise() {
			let extrinsic_count = <system::Module<T>>::extrinsic_count();
			(0..extrinsic_count).for_each(|index| {
				// Deposit `Charged` event if some amount of fee charged.
				let fee = <CurrentTransactionFee<T>>::take(index);
				if !fee.is_zero() {
					Self::deposit_event(RawEvent::Charged(index, fee));
				}
			});
		}
	}
}

decl_event!(
	pub enum Event<T> where Amount = AssetOf<T> {
		/// Fee charged (extrinsic_index, fee_amount)
		Charged(u32, Amount),
	}
);

decl_storage! {
	trait Store for Module<T: Trait> as Fees {
		/// The fee to be paid for making a transaction; the base.
		pub TransactionBaseFee get(transaction_base_fee) config(): AssetOf<T>;
		/// The fee to be paid for making a transaction; the per-byte portion.
		pub TransactionByteFee get(transaction_byte_fee) config(): AssetOf<T>;

		/// The `extrinsic_index => accumulated_fees` map, containing records to
		/// track the overall charged fees for each transaction.
		///
		/// All records should be removed at finalise stage.
		CurrentTransactionFee get(current_transaction_fee): map u32 => AssetOf<T>;
	}
}

impl<T: Trait> ChargeBytesFee<T::AccountId> for Module<T> {
	fn charge_base_bytes_fee(transactor: &T::AccountId, encoded_len: usize) -> Result {
		let bytes_fee = Self::transaction_byte_fee().checked_mul(
			&<AssetOf<T> as As<u64>>::sa(encoded_len as u64)
		).ok_or_else(|| "bytes fee overflow")?;
		let overall = Self::transaction_base_fee().checked_add(&bytes_fee).ok_or_else(|| "bytes fee overflow")?;
		Self::charge_fee(transactor, overall)
	}
}

impl<T: Trait> ChargeFee<T::AccountId> for Module<T> {
	type Amount = AssetOf<T>;

	fn charge_fee(transactor: &T::AccountId, amount: AssetOf<T>) -> Result {
		let extrinsic_index = <system::Module<T>>::extrinsic_index().ok_or_else(|| "no extrinsic index found")?;
		let current_fee = Self::current_transaction_fee(extrinsic_index);
		let new_fee = current_fee.checked_add(&amount).ok_or_else(|| "fee got overflow after charge")?;

		T::TransferAsset::withdraw(transactor, amount, WithdrawReason::TransactionPayment)?;

		<CurrentTransactionFee<T>>::insert(extrinsic_index, new_fee);
		Ok(())
	}

	fn refund_fee(transactor: &T::AccountId, amount: AssetOf<T>) -> Result {
		let extrinsic_index = <system::Module<T>>::extrinsic_index().ok_or_else(|| "no extrinsic index found")?;
		let current_fee = Self::current_transaction_fee(extrinsic_index);
		let new_fee = current_fee.checked_sub(&amount).ok_or_else(|| "fee got underflow after refund")?;

		T::TransferAsset::deposit(transactor, amount)?;

		<CurrentTransactionFee<T>>::insert(extrinsic_index, new_fee);
		Ok(())
	}
}
