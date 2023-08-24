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

//! # Asset Conversion Transaction Payment Pallet
//!
//! This pallet allows runtimes that include it to pay for transactions in assets other than the
//! chain's native asset.
//!
//! ## Overview
//!
//! This pallet provides a `SignedExtension` with an optional `AssetId` that specifies the asset
//! to be used for payment (defaulting to the native token on `None`). It expects an
//! [`OnChargeAssetTransaction`] implementation analogous to [`pallet-transaction-payment`]. The
//! included [`AssetConversionAdapter`] (implementing [`OnChargeAssetTransaction`]) determines the
//! fee amount by converting the fee calculated by [`pallet-transaction-payment`] in the native
//! asset into the amount required of the specified asset.
//!
//! ## Pallet API
//!
//! This pallet does not have any dispatchable calls or storage. It wraps FRAME's Transaction
//! Payment pallet and functions as a replacement. This means you should include both pallets in
//! your `construct_runtime` macro, but only include this pallet's [`SignedExtension`]
//! ([`ChargeAssetTxPayment`]).
//!
//! ## Terminology
//!
//! - Native Asset or Native Currency: The asset that a chain considers native, as in its default
//!   for transaction fee payment, deposits, inflation, etc.
//! - Other assets: Other assets that may exist on chain, for example under the Assets pallet.

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;

use codec::{Decode, Encode};
use frame_support::{
	dispatch::{DispatchInfo, DispatchResult, PostDispatchInfo},
	traits::{
		tokens::fungibles::{Balanced, Inspect},
		IsType,
	},
	DefaultNoBound,
};
use pallet_transaction_payment::OnChargeTransaction;
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{DispatchInfoOf, Dispatchable, PostDispatchInfoOf, SignedExtension, Zero},
	transaction_validity::{
		InvalidTransaction, TransactionValidity, TransactionValidityError, ValidTransaction,
	},
};

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

mod payment;
use frame_support::traits::tokens::AssetId;
use pallet_asset_conversion::MultiAssetIdConverter;
pub use payment::*;

/// Type aliases used for interaction with `OnChargeTransaction`.
pub(crate) type OnChargeTransactionOf<T> =
	<T as pallet_transaction_payment::Config>::OnChargeTransaction;
/// Balance type alias for balances of the chain's native asset.
pub(crate) type BalanceOf<T> = <OnChargeTransactionOf<T> as OnChargeTransaction<T>>::Balance;
/// Liquidity info type alias.
pub(crate) type LiquidityInfoOf<T> =
	<OnChargeTransactionOf<T> as OnChargeTransaction<T>>::LiquidityInfo;

/// Balance type alias for balances of assets that implement the `fungibles` trait.
pub(crate) type AssetBalanceOf<T> =
	<<T as Config>::Fungibles as Inspect<<T as frame_system::Config>::AccountId>>::Balance;
/// Type alias for Asset IDs.
pub(crate) type AssetIdOf<T> =
	<<T as Config>::Fungibles as Inspect<<T as frame_system::Config>::AccountId>>::AssetId;

/// Type alias for the interaction of balances with `OnChargeAssetTransaction`.
pub(crate) type ChargeAssetBalanceOf<T> =
	<<T as Config>::OnChargeAssetTransaction as OnChargeAssetTransaction<T>>::Balance;
/// Type alias for Asset IDs in their interaction with `OnChargeAssetTransaction`.
pub(crate) type ChargeAssetIdOf<T> =
	<<T as Config>::OnChargeAssetTransaction as OnChargeAssetTransaction<T>>::AssetId;
/// Liquidity info type alias for interaction with `OnChargeAssetTransaction`.
pub(crate) type ChargeAssetLiquidityOf<T> =
	<<T as Config>::OnChargeAssetTransaction as OnChargeAssetTransaction<T>>::LiquidityInfo;

/// Used to pass the initial payment info from pre- to post-dispatch.
#[derive(Encode, Decode, DefaultNoBound, TypeInfo)]
pub enum InitialPayment<T: Config> {
	/// No initial fee was paid.
	#[default]
	Nothing,
	/// The initial fee was paid in the native currency.
	Native(LiquidityInfoOf<T>),
	/// The initial fee was paid in an asset.
	Asset((LiquidityInfoOf<T>, BalanceOf<T>, AssetBalanceOf<T>)),
}

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::config]
	pub trait Config:
		frame_system::Config + pallet_transaction_payment::Config + pallet_asset_conversion::Config
	{
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
		/// The fungibles instance used to pay for transactions in assets.
		type Fungibles: Balanced<Self::AccountId>;
		/// The actual transaction charging logic that charges the fees.
		type OnChargeAssetTransaction: OnChargeAssetTransaction<Self>;
	}

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A transaction fee `actual_fee`, of which `tip` was added to the minimum inclusion fee,
		/// has been paid by `who` in an asset `asset_id`.
		AssetTxFeePaid {
			who: T::AccountId,
			actual_fee: AssetBalanceOf<T>,
			tip: BalanceOf<T>,
			asset_id: ChargeAssetIdOf<T>,
		},
		/// A swap of the refund in native currency back to asset failed.
		AssetRefundFailed { native_amount_kept: BalanceOf<T> },
	}
}

/// Require payment for transaction inclusion and optionally include a tip to gain additional
/// priority in the queue. Allows paying via both `Currency` as well as `fungibles::Balanced`.
///
/// Wraps the transaction logic in [`pallet_transaction_payment`] and extends it with assets.
/// An asset ID of `None` falls back to the underlying transaction payment logic via the native
/// currency.
#[derive(Encode, Decode, Clone, Eq, PartialEq, TypeInfo)]
#[scale_info(skip_type_params(T))]
pub struct ChargeAssetTxPayment<T: Config> {
	#[codec(compact)]
	tip: BalanceOf<T>,
	asset_id: Option<ChargeAssetIdOf<T>>,
}

impl<T: Config> ChargeAssetTxPayment<T>
where
	T::RuntimeCall: Dispatchable<Info = DispatchInfo, PostInfo = PostDispatchInfo>,
	AssetBalanceOf<T>: Send + Sync,
	BalanceOf<T>: Send + Sync + Into<ChargeAssetBalanceOf<T>> + From<ChargeAssetLiquidityOf<T>>,
	ChargeAssetIdOf<T>: Send + Sync,
{
	/// Utility constructor. Used only in client/factory code.
	pub fn from(tip: BalanceOf<T>, asset_id: Option<ChargeAssetIdOf<T>>) -> Self {
		Self { tip, asset_id }
	}

	/// Fee withdrawal logic that dispatches to either `OnChargeAssetTransaction` or
	/// `OnChargeTransaction`.
	fn withdraw_fee(
		&self,
		who: &T::AccountId,
		call: &T::RuntimeCall,
		info: &DispatchInfoOf<T::RuntimeCall>,
		len: usize,
	) -> Result<(BalanceOf<T>, InitialPayment<T>), TransactionValidityError> {
		let fee = pallet_transaction_payment::Pallet::<T>::compute_fee(len as u32, info, self.tip);
		debug_assert!(self.tip <= fee, "tip should be included in the computed fee");
		if fee.is_zero() {
			Ok((fee, InitialPayment::Nothing))
		} else if let Some(asset_id) = &self.asset_id {
			T::OnChargeAssetTransaction::withdraw_fee(
				who,
				call,
				info,
				asset_id.clone(),
				fee.into(),
				self.tip.into(),
			)
			.map(|(used_for_fee, received_exchanged, asset_consumed)| {
				(
					fee,
					InitialPayment::Asset((
						used_for_fee.into(),
						received_exchanged.into(),
						asset_consumed.into(),
					)),
				)
			})
		} else {
			<OnChargeTransactionOf<T> as OnChargeTransaction<T>>::withdraw_fee(
				who, call, info, fee, self.tip,
			)
			.map(|i| (fee, InitialPayment::Native(i)))
			.map_err(|_| -> TransactionValidityError { InvalidTransaction::Payment.into() })
		}
	}
}

impl<T: Config> sp_std::fmt::Debug for ChargeAssetTxPayment<T> {
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		write!(f, "ChargeAssetTxPayment<{:?}, {:?}>", self.tip, self.asset_id.encode())
	}
	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		Ok(())
	}
}

impl<T: Config> SignedExtension for ChargeAssetTxPayment<T>
where
	T::RuntimeCall: Dispatchable<Info = DispatchInfo, PostInfo = PostDispatchInfo>,
	AssetBalanceOf<T>: Send + Sync,
	BalanceOf<T>: Send
		+ Sync
		+ From<u64>
		+ Into<ChargeAssetBalanceOf<T>>
		+ Into<ChargeAssetLiquidityOf<T>>
		+ From<ChargeAssetLiquidityOf<T>>,
	ChargeAssetIdOf<T>: Send + Sync,
{
	const IDENTIFIER: &'static str = "ChargeAssetTxPayment";
	type AccountId = T::AccountId;
	type Call = T::RuntimeCall;
	type AdditionalSigned = ();
	type Pre = (
		// tip
		BalanceOf<T>,
		// who paid the fee
		Self::AccountId,
		// imbalance resulting from withdrawing the fee
		InitialPayment<T>,
		// asset_id for the transaction payment
		Option<ChargeAssetIdOf<T>>,
	);

	fn additional_signed(&self) -> sp_std::result::Result<(), TransactionValidityError> {
		Ok(())
	}

	fn validate(
		&self,
		who: &Self::AccountId,
		call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> TransactionValidity {
		use pallet_transaction_payment::ChargeTransactionPayment;
		let (fee, _) = self.withdraw_fee(who, call, info, len)?;
		let priority = ChargeTransactionPayment::<T>::get_priority(info, len, self.tip, fee);
		Ok(ValidTransaction { priority, ..Default::default() })
	}

	fn pre_dispatch(
		self,
		who: &Self::AccountId,
		call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> Result<Self::Pre, TransactionValidityError> {
		let (_fee, initial_payment) = self.withdraw_fee(who, call, info, len)?;
		Ok((self.tip, who.clone(), initial_payment, self.asset_id))
	}

	fn post_dispatch(
		pre: Option<Self::Pre>,
		info: &DispatchInfoOf<Self::Call>,
		post_info: &PostDispatchInfoOf<Self::Call>,
		len: usize,
		result: &DispatchResult,
	) -> Result<(), TransactionValidityError> {
		if let Some((tip, who, initial_payment, asset_id)) = pre {
			match initial_payment {
				InitialPayment::Native(already_withdrawn) => {
					debug_assert!(
						asset_id.is_none(),
						"For that payment type the `asset_id` should be None"
					);
					pallet_transaction_payment::ChargeTransactionPayment::<T>::post_dispatch(
						Some((tip, who, already_withdrawn)),
						info,
						post_info,
						len,
						result,
					)?;
				},
				InitialPayment::Asset(already_withdrawn) => {
					debug_assert!(
						asset_id.is_some(),
						"For that payment type the `asset_id` should be set"
					);
					let actual_fee = pallet_transaction_payment::Pallet::<T>::compute_actual_fee(
						len as u32, info, post_info, tip,
					);

					if let Some(asset_id) = asset_id {
						let (used_for_fee, received_exchanged, asset_consumed) = already_withdrawn;
						let converted_fee = T::OnChargeAssetTransaction::correct_and_deposit_fee(
							&who,
							info,
							post_info,
							actual_fee.into(),
							tip.into(),
							used_for_fee.into(),
							received_exchanged.into(),
							asset_id.clone(),
							asset_consumed.into(),
						)?;

						Pallet::<T>::deposit_event(Event::<T>::AssetTxFeePaid {
							who,
							actual_fee: converted_fee,
							tip,
							asset_id,
						});
					}
				},
				InitialPayment::Nothing => {
					// `actual_fee` should be zero here for any signed extrinsic. It would be
					// non-zero here in case of unsigned extrinsics as they don't pay fees but
					// `compute_actual_fee` is not aware of them. In both cases it's fine to just
					// move ahead without adjusting the fee, though, so we do nothing.
					debug_assert!(tip.is_zero(), "tip should be zero if initial fee was zero.");
				},
			}
		}

		Ok(())
	}
}
