// Copyright (C) 2021-2023 Parity Technologies (UK) Ltd.
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
use frame_support::{ensure, unsigned::TransactionValidityError, Deserialize, Serialize};
use pallet_transaction_payment::OnChargeTransaction;
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{DispatchInfoOf, MaybeSerializeDeserialize, PostDispatchInfoOf},
	transaction_validity::InvalidTransaction,
};
use sp_std::{fmt::Debug, marker::PhantomData};
/// Handle withdrawing, refunding and depositing of transaction fees.
pub trait OnChargeAssetTransactionBySwap<T: Config> {
	/// The type used to identify the assets used for transaction payments.
	type AssetId: FullCodec + Copy + MaybeSerializeDeserialize + Debug + Default + Eq + TypeInfo;

	/// Before the transaction is executed the payment of the transaction fees needs to be secured.
	///
	/// Note: The `fee` already includes the `tip`.
	fn withdraw_fee(
		who: &T::AccountId,
		call: &T::RuntimeCall,
		dispatch_info: &DispatchInfoOf<T::RuntimeCall>,
		asset_id: Self::AssetId,
		fee: BalanceOf<T>,
		tip: BalanceOf<T>,
	) -> Result<
		<T::OnChargeTransaction as OnChargeTransaction<T>>::LiquidityInfo,
		TransactionValidityError,
	>;

	/// After the transaction was executed the actual fee can be calculated.
	/// This function should refund any overpaid fees and optionally deposit
	/// the corrected amount.
	///
	/// Note: The `fee` already includes the `tip`.
	fn correct_and_deposit_fee(
		who: &T::AccountId,
		dispatch_info: &DispatchInfoOf<T::RuntimeCall>,
		post_info: &PostDispatchInfoOf<T::RuntimeCall>,
		corrected_fee: BalanceOf<T>,
		tip: BalanceOf<T>,
		already_withdrawn: <T::OnChargeTransaction as OnChargeTransaction<T>>::LiquidityInfo,
	) -> Result<(), TransactionValidityError>;
}

/// Implements the asset transaction for a balance to asset converter (implementing
/// [`SwapForNative`]).
///
/// The converter is given the complete fee in terms of the asset used for the transaction.
pub struct FungiblesAdapter<CON>(PhantomData<CON>);

/// Default implementation for a runtime instantiating this pallet, an asset to native swapper.
impl<T, CON> OnChargeAssetTransactionBySwap<T> for FungiblesAdapter<CON>
where
	T: Config,
	CON: SwapForNative<
		T::RuntimeOrigin,
		T::AccountId,
		BalanceOf<T>,
		AssetBalanceOf<T>,
		AssetIdOf<T>,
	>,
	AssetIdOf<T>: Default + Serialize,
	AssetIdOf<T>: for<'de> Deserialize<'de>,
{
	type AssetId = AssetIdOf<T>;

	/// Withdraw the predicted fee from the transaction origin.
	///
	/// Note: The `fee` already includes the `tip`.
	fn withdraw_fee(
		who: &T::AccountId,
		_call: &T::RuntimeCall,
		_info: &DispatchInfoOf<T::RuntimeCall>,
		asset_id: Self::AssetId,
		fee: BalanceOf<T>,
		_tip: BalanceOf<T>,
	) -> Result<
		<T::OnChargeTransaction as OnChargeTransaction<T>>::LiquidityInfo,
		TransactionValidityError,
	> {
		let asset_consumed =
			CON::swap_tokens_for_exact_native(who.clone(), asset_id, fee, None, who.clone(), true)
				.map_err(|_| TransactionValidityError::from(InvalidTransaction::Payment))?;

		// We don't know the precision of the underlying asset. Because the converted fee could be
		// less than one (e.g. 0.5) but gets rounded down by integer division we introduce a minimum
		// fee.
		ensure!(asset_consumed > Zero::zero(), InvalidTransaction::Payment);

		<T::OnChargeTransaction>::withdraw_fee(who, _call, _info, fee, _tip)
	}

	/// Delegate to the OnChargeTransaction functionality.
	///
	/// Note: The `corrected_fee` already includes the `tip`.
	fn correct_and_deposit_fee(
		who: &T::AccountId,
		_dispatch_info: &DispatchInfoOf<T::RuntimeCall>,
		_post_info: &PostDispatchInfoOf<T::RuntimeCall>,
		corrected_fee: BalanceOf<T>,
		_tip: BalanceOf<T>,
		paid: <T::OnChargeTransaction as OnChargeTransaction<T>>::LiquidityInfo,
	) -> Result<(), TransactionValidityError> {
		// Refund to the account that paid the fees. If this fails, the account might have
		// dropped below the existential balance. In that case we don't refund anything.
		//
		// NOTE: We do not automatically convert the native token back to the asset,
		// otherwise the fee could go back and forth between the two currencies paying dex
		// charges each time over the course of several transactions. It's better for the user
		// that it stays in native and smart wallets can realise there's enough native to not
		// need to pay the next transaction using an asset.
		<T::OnChargeTransaction>::correct_and_deposit_fee(
			who,
			_dispatch_info,
			_post_info,
			corrected_fee,
			_tip,
			paid,
		)
	}
}
