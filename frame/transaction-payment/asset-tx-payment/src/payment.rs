// Copyright (C) Parity Technologies (UK) Ltd.
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

///! Traits and default implementation for paying transaction fees in assets.
use super::*;
use crate::Config;

use codec::FullCodec;
use frame_support::{
	ensure,
	traits::{fungibles::SwapNative, tokens::Balance},
	unsigned::TransactionValidityError,
};
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{DispatchInfoOf, MaybeSerializeDeserialize, PostDispatchInfoOf},
	transaction_validity::InvalidTransaction,
};
use sp_std::{fmt::Debug, marker::PhantomData};

/// Handle withdrawing, refunding and depositing of transaction fees.
pub trait OnChargeAssetTransaction<T: Config> {
	/// The underlying integer type in which fees are calculated.
	type Balance: Balance;
	/// The type used to identify the assets used for transaction payment.
	type AssetId: FullCodec + Copy + MaybeSerializeDeserialize + Debug + Default + Eq + TypeInfo;
	/// The type used to store the intermediate values between pre- and post-dispatch.
	type LiquidityInfo;

	/// Before the transaction is executed the payment of the transaction fees needs to be secured.
	///
	/// Note: The `fee` already includes the `tip`.
	fn withdraw_fee(
		who: &T::AccountId,
		call: &T::RuntimeCall,
		dispatch_info: &DispatchInfoOf<T::RuntimeCall>,
		asset_id: Self::AssetId,
		fee: Self::Balance,
		tip: Self::Balance,
	) -> Result<Self::LiquidityInfo, TransactionValidityError>;

	/// After the transaction was executed the actual fee can be calculated.
	/// This function should refund any overpaid fees and optionally deposit
	/// the corrected amount.
	///
	/// Note: The `fee` already includes the `tip`.
	///
	/// Returns the fee and tip in the asset used for payment as (fee, tip).
	fn correct_and_deposit_fee(
		who: &T::AccountId,
		dispatch_info: &DispatchInfoOf<T::RuntimeCall>,
		post_info: &PostDispatchInfoOf<T::RuntimeCall>,
		corrected_fee: Self::Balance,
		tip: Self::Balance,
		already_paid: Self::LiquidityInfo,
		asset_id: Self::AssetId,
	) -> Result<(), TransactionValidityError>;
}

/// Implements the asset transaction for a balance to asset converter (implementing
/// [`SwapNative`]).
///
/// The converter is given the complete fee in terms of the asset used for the transaction.
pub struct AssetConversionAdapter<CON>(PhantomData<CON>);

/// Default implementation for a runtime instantiating this pallet, an asset to native swapper.
impl<T, CON> OnChargeAssetTransaction<T> for AssetConversionAdapter<CON>
where
	T: Config,
	CON: SwapNative<T::RuntimeOrigin, T::AccountId, BalanceOf<T>, AssetBalanceOf<T>, AssetIdOf<T>>,
	AssetIdOf<T>: FullCodec + Copy + MaybeSerializeDeserialize + Debug + Default + Eq + TypeInfo,
{
	type Balance = BalanceOf<T>;
	type AssetId = AssetIdOf<T>;
	type LiquidityInfo = BalanceOf<T>;

	/// Withdraw the predicted fee from the transaction origin.
	///
	/// Note: The `fee` already includes the `tip`.
	fn withdraw_fee(
		who: &T::AccountId,
		call: &T::RuntimeCall,
		info: &DispatchInfoOf<T::RuntimeCall>,
		asset_id: Self::AssetId,
		fee: BalanceOf<T>,
		tip: BalanceOf<T>,
	) -> Result<Self::LiquidityInfo, TransactionValidityError> {
		// convert the asset into native currency
		// TODO: add ED if needed to the `fee`

		// 0.1001 DOT
		let swap_amount = fee;
		let asset_consumed = CON::swap_tokens_for_exact_native(
			who.clone(),
			asset_id,
			swap_amount,
			None,
			who.clone(),
			true,
		)
		.map_err(|_| TransactionValidityError::from(InvalidTransaction::Payment))?;

		ensure!(asset_consumed > Zero::zero(), InvalidTransaction::Payment);

		// charge the fee in native currency
		<T::OnChargeTransaction>::withdraw_fee(who, call, info, fee, tip)?;

		// 0.1 DOT should be left
		Ok(swap_amount)
	}

	/// Delegate to the OnChargeTransaction functionality.
	///
	/// Note: The `corrected_fee` already includes the `tip`.
	fn correct_and_deposit_fee(
		who: &T::AccountId,
		_dispatch_info: &DispatchInfoOf<T::RuntimeCall>,
		_post_info: &PostDispatchInfoOf<T::RuntimeCall>,
		corrected_fee: BalanceOf<T>, // 0.00005 DOT
		_tip: BalanceOf<T>,
		already_paid: Self::LiquidityInfo, // 0.1001 DOT ?
		asset_id: Self::AssetId,
	) -> Result<(), TransactionValidityError> {
		// Refund to the account that paid the fees. If this fails, the account might have
		// dropped below the existential balance. In that case we don't refund anything.

		// swap the difference of `already_paid` - `corrected_fee`
		let swap_amount = already_paid - corrected_fee;
		let _asset_received = CON::swap_exact_native_for_tokens(
			who.clone(),
			asset_id,
			swap_amount,
			None,
			who.clone(),
			true, // todo: false?
		)
		.map_err(|_| TransactionValidityError::from(InvalidTransaction::Payment))?;

		Ok(())
	}
}
