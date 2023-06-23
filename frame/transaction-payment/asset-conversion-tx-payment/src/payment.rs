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
	traits::{fungible::Inspect, fungibles::SwapNative, tokens::Balance},
	unsigned::TransactionValidityError,
};
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{DispatchInfoOf, MaybeSerializeDeserialize, PostDispatchInfoOf, Zero},
	transaction_validity::InvalidTransaction,
	Saturating,
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

	/// Secure the payment of the transaction fees before the transaction is executed.
	///
	/// Note: The `fee` already includes the `tip`.
	fn withdraw_fee(
		who: &T::AccountId,
		call: &T::RuntimeCall,
		dispatch_info: &DispatchInfoOf<T::RuntimeCall>,
		asset_id: Self::AssetId,
		fee: Self::Balance,
		tip: Self::Balance,
	) -> Result<
		(LiquidityInfoOf<T>, Self::LiquidityInfo, AssetBalanceOf<T>),
		TransactionValidityError,
	>;

	/// Refund any overpaid fees and deposit the corrected amount.
	/// The actual fee gets calculated once the transaction is executed.
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
		fee_paid: LiquidityInfoOf<T>,
		received_exchanged: Self::LiquidityInfo,
		asset_id: Self::AssetId,
		initial_asset_consumed: AssetBalanceOf<T>,
	) -> Result<AssetBalanceOf<T>, TransactionValidityError>;
}

/// Implements the asset transaction for a balance to asset converter (implementing
/// [`SwapNative`]).
///
/// The converter is given the complete fee in terms of the asset used for the transaction.
pub struct AssetConversionAdapter<C, CON>(PhantomData<(C, CON)>);

/// Default implementation for a runtime instantiating this pallet, an asset to native swapper.
impl<T, C, CON> OnChargeAssetTransaction<T> for AssetConversionAdapter<C, CON>
where
	T: Config,
	C: Inspect<<T as frame_system::Config>::AccountId>,
	CON: SwapNative<T::RuntimeOrigin, T::AccountId, BalanceOf<T>, AssetBalanceOf<T>, AssetIdOf<T>>,
	AssetIdOf<T>: FullCodec + Copy + MaybeSerializeDeserialize + Debug + Default + Eq + TypeInfo,
	BalanceOf<T>: IsType<<C as Inspect<<T as frame_system::Config>::AccountId>>::Balance>,
{
	type Balance = BalanceOf<T>;
	type AssetId = AssetIdOf<T>;
	type LiquidityInfo = BalanceOf<T>;

	/// Swap & withdraw the predicted fee from the transaction origin.
	///
	/// Note: The `fee` already includes the `tip`.
	///
	/// Returns the total amount in native currency received by exchanging the `asset_id` and the
	/// amount in native currency used to pay the fee.
	fn withdraw_fee(
		who: &T::AccountId,
		call: &T::RuntimeCall,
		info: &DispatchInfoOf<T::RuntimeCall>,
		asset_id: Self::AssetId,
		fee: BalanceOf<T>,
		tip: BalanceOf<T>,
	) -> Result<
		(LiquidityInfoOf<T>, Self::LiquidityInfo, AssetBalanceOf<T>),
		TransactionValidityError,
	> {
		// convert the asset into native currency
		let ed = C::minimum_balance();
		let native_asset_required =
			if C::balance(&who) >= ed.saturating_add(fee.into()) { fee } else { fee + ed.into() };

		let asset_consumed = CON::swap_tokens_for_exact_native(
			who.clone(),
			asset_id,
			native_asset_required,
			None,
			who.clone(),
			true,
		)
		.map_err(|_| TransactionValidityError::from(InvalidTransaction::Payment))?;

		ensure!(asset_consumed > Zero::zero(), InvalidTransaction::Payment);

		// charge the fee in native currency
		<T::OnChargeTransaction>::withdraw_fee(who, call, info, fee, tip)
			.map(|r| (r, native_asset_required, asset_consumed))
	}

	/// Correct the fee and swap the refund back to asset.
	///
	/// Note: The `corrected_fee` already includes the `tip`.
	/// Note: Is the ED wasn't needed, the `received_exchanged` will be equal to `fee_paid`, or
	/// `fee_paid + ed` otherwise.
	fn correct_and_deposit_fee(
		who: &T::AccountId,
		dispatch_info: &DispatchInfoOf<T::RuntimeCall>,
		post_info: &PostDispatchInfoOf<T::RuntimeCall>,
		corrected_fee: BalanceOf<T>,
		tip: BalanceOf<T>,
		fee_paid: LiquidityInfoOf<T>,
		received_exchanged: Self::LiquidityInfo,
		asset_id: Self::AssetId,
		initial_asset_consumed: AssetBalanceOf<T>,
	) -> Result<AssetBalanceOf<T>, TransactionValidityError> {
		// Refund the native asset to the account that paid the fees (`who`).
		// The `who` account will receive the "fee_paid - corrected_fee" refund.
		<T::OnChargeTransaction>::correct_and_deposit_fee(
			who,
			dispatch_info,
			post_info,
			corrected_fee,
			tip,
			fee_paid,
		)?;

		// calculate the refund in native asset, to swap back to the desired `asset_id`
		let swap_back = received_exchanged.saturating_sub(corrected_fee);
		let mut asset_refund = Zero::zero();
		if !swap_back.is_zero() {
			// If this fails, the account might have dropped below the existential balance or there
			// is not enough liquidity left in the pool. In that case we don't throw an error and
			// the account will keep the native currency.
			match CON::swap_exact_native_for_tokens(
				who.clone(), // we already deposited the native to `who`
				asset_id,    // we want asset_id back
				swap_back,   // amount of the native asset to convert to `asset_id`
				None,        // no minimum amount back
				who.clone(), // we will refund to `who`
				false,       // no need to keep alive
			)
			.ok()
			{
				Some(acquired) => asset_refund = acquired,
				None => {
					Pallet::<T>::deposit_event(Event::<T>::AssetRefundFailed {
						native_amount_kept: swap_back,
					});
				},
			}
		}

		let actual_paid = initial_asset_consumed.saturating_sub(asset_refund);
		Ok(actual_paid)
	}
}
