// Copyright 2020 Parity Technologies (UK) Ltd.
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
// along with Substrate. If not, see <http://www.gnu.org/licenses/>.

use crate::{Call, GasPrice, GasUsageReport, NegativeImbalanceOf, Trait};
use frame_support::{
	storage::StorageValue,
	traits::{Currency, ExistenceRequirement, Imbalance, OnUnbalanced, WithdrawReason},
	weights::{DispatchInfo, Weight},
	IsSubType,
};
use sp_runtime::{
	traits::{CheckedDiv, Convert, SignedExtension, UniqueSaturatedInto},
	transaction_validity::{
		InvalidTransaction, TransactionValidity, TransactionValidityError, ValidTransaction,
	},
};
use sp_std::{convert::TryFrom, fmt, marker::PhantomData, prelude::*};

#[doc(hidden)]
#[cfg_attr(test, derive(Debug))]
pub struct DynamicWeightData<AccountId, NegativeImbalance> {
	/// The account id who should receive the refund from the gas leftovers.
	transactor: AccountId,
	/// The negative imbalance obtained by withdrawing the value up to the requested gas limit.
	imbalance: NegativeImbalance,
}

/// A `SignedExtension` required to properly handle gas limits requested by contract executing
/// transactions.
#[derive(codec::Encode, codec::Decode, Clone, Eq, PartialEq)]
pub struct GasWeightConversion<T: Trait + Send + Sync>(PhantomData<T>);

impl<T: Trait + Send + Sync> GasWeightConversion<T> {
	pub fn new() -> Self {
		Self(PhantomData)
	}

	/// Perform pre-dispatch checks for the given call and origin.
	fn perform_pre_dispatch_checks(
		who: &T::AccountId,
		call: &<T as Trait>::Call,
	) -> Result<
		Option<DynamicWeightData<T::AccountId, NegativeImbalanceOf<T>>>,
		TransactionValidityError,
	> {
		// This signed extension only deals with this module's `Call`.
		let call = match call.is_sub_type() {
			Some(call) => call,
			None => return Ok(None),
		};

		match *call {
			Call::claim_surcharge(_, _) | Call::update_schedule(_) | Call::put_code(_) => Ok(None),
			Call::call(_, _, gas_limit, _) | Call::instantiate(_, gas_limit, _, _) => {
				// Compute how much block weight this transaction can take at its limit, i.e.
				// if this transaction depleted all provided gas to zero.
				let gas_weight_limit = Weight::try_from(gas_limit)
					.map_err(|_| InvalidTransaction::ExhaustsResources)?;
				let weight_available = <frame_system::Module<T>>::remaining_weight().into();
				if gas_weight_limit > weight_available {
					// We discard the transaction if the requested limit exceeds the available
					// amount of weight in the current block.
					//
					// Note that this transaction is left out only from the current block and txq
					// might attempt to include this transaction again.
					return Err(InvalidTransaction::ExhaustsResources.into());
				}

				// Compute the fee corresponding for the given gas_weight_limit and attempt
				// withdrawing from the origin of this transaction.
				let fee = T::WeightToFee::convert(gas_weight_limit);

				// Compute and store the effective price per unit of gas.
				let gas_price = {
					let divisor = gas_weight_limit.unique_saturated_into();
					fee.checked_div(&divisor).unwrap_or(1.into())
				};

				//
				// The place where we set GasPrice for the execution of this transaction.
				//
				<GasPrice<T>>::put(gas_price);

				let imbalance = match T::Currency::withdraw(
					who,
					fee,
					WithdrawReason::TransactionPayment.into(),
					ExistenceRequirement::KeepAlive,
				) {
					Ok(imbalance) => imbalance,
					Err(_) => return Err(InvalidTransaction::Payment.into()),
				};

				Ok(Some(DynamicWeightData {
					transactor: who.clone(),
					imbalance,
				}))
			}
			Call::__PhantomItem(_, _) => unreachable!("Variant is never constructed"),
		}
	}
}

impl<T: Trait + Send + Sync> Default for GasWeightConversion<T> {
	fn default() -> Self {
		Self(PhantomData)
	}
}

impl<T: Trait + Send + Sync> fmt::Debug for GasWeightConversion<T> {
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "GasWeightConversion")
	}

	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		Ok(())
	}
}

impl<T: Trait + Send + Sync> SignedExtension for GasWeightConversion<T> {
	const IDENTIFIER: &'static str = "GasWeightConversion";
	type AccountId = T::AccountId;
	type Call = <T as Trait>::Call;
	type AdditionalSigned = ();
	type DispatchInfo = DispatchInfo;
	/// Optional pre-dispatch check data.
	///
	/// It is present only for the contract calls that operate with gas.
	type Pre = Option<DynamicWeightData<T::AccountId, NegativeImbalanceOf<T>>>;

	fn additional_signed(&self) -> Result<(), TransactionValidityError> {
		Ok(())
	}

	fn pre_dispatch(
		self,
		who: &Self::AccountId,
		call: &Self::Call,
		_: DispatchInfo,
		_: usize,
	) -> Result<Self::Pre, TransactionValidityError> {
		Self::perform_pre_dispatch_checks(who, call)
	}

	fn validate(
		&self,
		who: &Self::AccountId,
		call: &Self::Call,
		_: Self::DispatchInfo,
		_: usize,
	) -> TransactionValidity {
		Self::perform_pre_dispatch_checks(who, call).map(|_| ValidTransaction::default())
	}

	fn post_dispatch(pre: Self::Pre, _info: DispatchInfo, _len: usize) {
		if let Some(DynamicWeightData {
			transactor,
			imbalance,
		}) = pre
		{
			// Take the report of consumed and left gas after the execution of the current
			// transaction.
			let (gas_left, gas_spent) = GasUsageReport::take();

			// These should be OK since we don't buy more
			let unused_weight = gas_left as Weight;
			let spent_weight = gas_spent as Weight;

			let refund = T::WeightToFee::convert(unused_weight);

			// Refund the unused gas.
			let refund_imbalance = T::Currency::deposit_creating(&transactor, refund);
			if let Ok(imbalance) = imbalance.offset(refund_imbalance) {
				T::GasPayment::on_unbalanced(imbalance);
			}

			<frame_system::Module<T>>::register_extra_weight_unchecked(spent_weight);
		}
	}
}
