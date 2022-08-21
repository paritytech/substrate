// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

//! # Asset Transaction Payment Pallet
//!
//! This pallet allows runtimes that include it to pay for transactions in assets other than the
//! main token of the chain.
//!
//! ## Overview

//! It does this by extending transactions to include an optional `AssetId` that specifies the asset
//! to be used for payment (defaulting to the native token on `None`). It expects an
//! [`OnChargeAssetTransaction`] implementation analogously to [`pallet-transaction-payment`]. The
//! included [`FungiblesAdapter`] (implementing [`OnChargeAssetTransaction`]) determines the fee
//! amount by converting the fee calculated by [`pallet-transaction-payment`] into the desired
//! asset.
//!
//! Optionally allows configure default payment asset per account.
//!
//! ## Integration

//! This pallet wraps FRAME's transaction payment pallet and functions as a replacement. This means
//! you should include both pallets in your `construct_runtime` macro, but only include this
//! pallet's [`SignedExtension`] ([`ChargeAssetTxPayment`]).

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;

use codec::{Decode, Encode};
use frame_support::{
	dispatch::{DispatchInfo, DispatchResult, PostDispatchInfo},
	pallet_prelude::*,
	traits::{
		tokens::{
			fungibles::{Balanced, CreditOf, Inspect, MutateHold},
			BalanceConversion, WithdrawConsequence,
		},
		Get, IsSubType, IsType,
	},
	DefaultNoBound,
};
use frame_system::pallet_prelude::*;

use pallet_transaction_payment::OnChargeTransaction;
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{DispatchInfoOf, Dispatchable, PostDispatchInfoOf, SignedExtension, Zero},
	transaction_validity::{
		InvalidTransaction, TransactionValidity, TransactionValidityError, ValidTransaction,
	},
	FixedPointOperand,
};

#[cfg(test)]
mod tests;

mod benchmarking;

mod payment;
pub mod weights;
pub use payment::*;
pub use weights::*;

// Type aliases used for interaction with `OnChargeTransaction`.
pub(crate) type OnChargeTransactionOf<T> =
	<T as pallet_transaction_payment::Config>::OnChargeTransaction;
// Balance type alias.
pub(crate) type BalanceOf<T> = <OnChargeTransactionOf<T> as OnChargeTransaction<T>>::Balance;
// Liquity info type alias.
pub(crate) type LiquidityInfoOf<T> =
	<OnChargeTransactionOf<T> as OnChargeTransaction<T>>::LiquidityInfo;

// Type alias used for interaction with fungibles (assets).
// Balance type alias.
pub(crate) type AssetBalanceOf<T> =
	<<T as Config>::Fungibles as Inspect<<T as frame_system::Config>::AccountId>>::Balance;
/// Asset id type alias.
pub(crate) type AssetIdOf<T> =
	<<T as Config>::Fungibles as Inspect<<T as frame_system::Config>::AccountId>>::AssetId;

// Type aliases used for interaction with `OnChargeAssetTransaction`.
// Balance type alias.
pub(crate) type ChargeAssetBalanceOf<T> =
	<<T as Config>::OnChargeAssetTransaction as OnChargeAssetTransaction<T>>::Balance;
// Asset id type alias.
pub(crate) type ChargeAssetIdOf<T> =
	<<T as Config>::OnChargeAssetTransaction as OnChargeAssetTransaction<T>>::AssetId;
// Liquity info type alias.
pub(crate) type ChargeAssetLiquidityOf<T> =
	<<T as Config>::OnChargeAssetTransaction as OnChargeAssetTransaction<T>>::LiquidityInfo;

/// Used to pass the initial payment info from pre- to post-dispatch.
#[derive(Encode, Decode, DefaultNoBound, TypeInfo)]
pub enum InitialPayment<T: Config> {
	/// No initial fee was payed.
	Nothing,
	/// The initial fee was payed in the native currency.
	Native(LiquidityInfoOf<T>),
	/// The initial fee was payed in an asset.
	Asset(CreditOf<T::AccountId, T::Fungibles>),
}

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use frame_support::{dispatch::GetDispatchInfo, traits::IsSubType};

	use super::*;

	#[pallet::config]
	pub trait Config: frame_system::Config + pallet_transaction_payment::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
		/// The fungibles instance used to pay for transactions in assets.
		type Fungibles: Balanced<Self::AccountId>;

		/// The actual transaction charging logic that charges the fees.
		type OnChargeAssetTransaction: OnChargeAssetTransaction<Self>;

		/// Use configured default asset per user.
		/// If true, each transaction will requires one storage access.
		/// If false, it is zero cost, but user still allows to configure default per user asset.
		/// That can be used by wallet to peek asset to send in header.
		#[pallet::constant]
		type UseUserConfiguration: Get<bool>;

		type WeightInfo: WeightInfo;

		/// origin allowed to reset payment asset for any account
		type ConfigurationOrigin: EnsureOrigin<Self::Origin>;

		/// Amount native assets to lock of ED.
		/// Non native equivalent of asset is locked as defined by `BalanceConverter` at time of
		/// call.
		type ConfigurationExistentialDeposit: Get<BalanceOf<Self>>;

		type PayableCall: Parameter
			+ From<frame_system::Call<Self>>
			+ Dispatchable<Origin = Self::Origin, PostInfo = PostDispatchInfo, Info = DispatchInfo>
			+ GetDispatchInfo
			+ IsSubType<Call<Self>>
			+ IsType<<Self as frame_system::Config>::RuntimeCall>;

		type Lock: MutateHold<
			Self::AccountId,
			AssetId = ChargeAssetIdOf<Self>,
			Balance = ChargeAssetBalanceOf<Self>,
		>;
		/// To covert ED to other asset amount.
		type BalanceConverter: BalanceConversion<
			BalanceOf<Self>,
			ChargeAssetIdOf<Self>,
			ChargeAssetBalanceOf<Self>,
		>;
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A transaction fee `actual_fee`, of which `tip` was added to the minimum inclusion fee,
		/// has been paid by `who` in an asset `asset_id`.
		AssetTxFeePaid {
			who: T::AccountId,
			actual_fee: BalanceOf<T>,
			tip: BalanceOf<T>,
			asset_id: Option<ChargeAssetIdOf<T>>,
		},
	}

	/// Stores default payment asset of user with ED locked.
	#[pallet::storage]
	#[pallet::getter(fn payment_assets)]
	pub type PaymentAssets<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		T::AccountId,
		(ChargeAssetIdOf<T>, ChargeAssetBalanceOf<T>),
		OptionQuery,
	>;

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Sets or resets payment asset.
		///
		/// If `asset_id` is `None`, then native asset is used.
		/// Else new asset is configured and ED is on hold.
		#[pallet::weight(T::WeightInfo::set_payment_asset())]
		pub fn set_payment_asset(
			origin: OriginFor<T>,
			payer: T::AccountId,
			asset_id: Option<ChargeAssetIdOf<T>>,
		) -> DispatchResult {
			// either configuration origin or owner of configuration
			if let Err(origin) = T::ConfigurationOrigin::try_origin(origin) {
				let who = ensure_signed(origin)?;
				ensure!(who == payer, DispatchError::BadOrigin,)
			};

			// clean previous configuration
			if let Some((asset_id, ed)) = <PaymentAssets<T>>::get(&payer) {
				T::Lock::release(asset_id, &payer, ed, true)?;
				<PaymentAssets<T>>::remove(&payer);
			}

			// configure new payment asset and hold some ed
			if let Some(asset_id) = asset_id {
				let ed = T::BalanceConverter::to_asset_balance(
					T::ConfigurationExistentialDeposit::get(),
					asset_id,
				)
				.map_err(|_| DispatchError::Other("Cannot convert ED to asset balance"))?;
				T::Lock::hold(asset_id, &payer, ed)?;
				<PaymentAssets<T>>::insert(payer, (asset_id, ed));
			}

			Ok(())
		}
	}

	impl<T: Config> Pallet<T> {}
}

/// Require the transactor pay for themselves and maybe include a tip to gain additional priority
/// in the queue. Allows paying via both `Currency` as well as `fungibles::Balanced`.
///
/// Wraps the transaction logic in [`pallet_transaction_payment`] and extends it with assets.
/// An asset id of `None` falls back to the underlying transaction payment via the native currency.
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
	AssetBalanceOf<T>: Send + Sync + FixedPointOperand,
	BalanceOf<T>: Send + Sync + FixedPointOperand + IsType<ChargeAssetBalanceOf<T>>,
	ChargeAssetIdOf<T>: Send + Sync,
	CreditOf<T::AccountId, T::Fungibles>: IsType<ChargeAssetLiquidityOf<T>>,
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
		asset_id: Option<ChargeAssetIdOf<T>>,
	) -> Result<(BalanceOf<T>, InitialPayment<T>), TransactionValidityError> {
		let fee = pallet_transaction_payment::Pallet::<T>::compute_fee(len as u32, info, self.tip);
		debug_assert!(self.tip <= fee, "tip should be included in the computed fee");
		if fee.is_zero() {
			Ok((fee, InitialPayment::Nothing))
		} else if let Some(asset_id) = asset_id {
			T::OnChargeAssetTransaction::withdraw_fee(
				who,
				call,
				info,
				asset_id,
				fee.into(),
				self.tip.into(),
			)
			.map(|i| (fee, InitialPayment::Asset(i.into())))
		} else {
			<OnChargeTransactionOf<T> as OnChargeTransaction<T>>::withdraw_fee(
				who, call, info, fee, self.tip,
			)
			.map(|i| (fee, InitialPayment::Native(i)))
			.map_err(|_| -> TransactionValidityError { InvalidTransaction::Payment.into() })
		}
	}

	/// Get payment asset for this transaction.
	///
	/// Will pick asset id in next order:
	/// - defined in extra
	/// - defined in well known call
	/// - defined in configuration
	/// - native
	fn get_payment_asset(
		&self,
		who: &T::AccountId,
		call: &T::RuntimeCall,
	) -> Option<ChargeAssetIdOf<T>> {
		if self.asset_id.is_some() || !<T as Config>::UseUserConfiguration::get() {
			return self.asset_id
		}

		let call = <T as Config>::PayableCall::from_ref(call);
		match call.is_sub_type() {
			Some(Call::set_payment_asset { asset_id, .. }) => asset_id.to_owned(),
			_ => <PaymentAssets<T>>::get(who).map(|x| x.0),
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
	AssetBalanceOf<T>: Send + Sync + FixedPointOperand,
	BalanceOf<T>: Send + Sync + From<u64> + FixedPointOperand + IsType<ChargeAssetBalanceOf<T>>,
	ChargeAssetIdOf<T>: Send + Sync,
	CreditOf<T::AccountId, T::Fungibles>: IsType<ChargeAssetLiquidityOf<T>>,
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
		let asset_id = self.get_payment_asset(who, call);
		let (fee, _) = self.withdraw_fee(who, call, info, len, asset_id)?;
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
		let asset_id = self.get_payment_asset(who, call);
		let (_fee, initial_payment) = self.withdraw_fee(who, call, info, len, asset_id)?;
		Ok((self.tip, who.clone(), initial_payment, asset_id))
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
					pallet_transaction_payment::ChargeTransactionPayment::<T>::post_dispatch(
						Some((tip, who, already_withdrawn)),
						info,
						post_info,
						len,
						result,
					)?;
				},
				InitialPayment::Asset(already_withdrawn) => {
					let actual_fee = pallet_transaction_payment::Pallet::<T>::compute_actual_fee(
						len as u32, info, post_info, tip,
					);
					T::OnChargeAssetTransaction::correct_and_deposit_fee(
						&who,
						info,
						post_info,
						actual_fee.into(),
						tip.into(),
						already_withdrawn.into(),
					)?;
					Pallet::<T>::deposit_event(Event::<T>::AssetTxFeePaid {
						who,
						actual_fee,
						tip,
						asset_id,
					});
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
