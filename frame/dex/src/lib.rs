// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! # Substrate DEX
//!
//! Substrate DEX pallet based on [Uniswap V2](https://github.com/Uniswap/v2-core) logic.
//!
//! ## Overview
//!
//! This pallet allows to:
//!
//!  - create a liquidity pool for 2 assets
//!  - provide the liquidity and receive back an LP token
//!  - exchange the LP token back to assets
//!  - swap 2 assets if there is a pool created
//!  - query for an exchange price via a new runtime call endpoint
//!
//! Here is an example `state_call` that asks for a quote of a pool of native versus asset 1:
//!
//! ```text
//! curl -sS -H "Content-Type: application/json" -d \
//! '{"id":1, "jsonrpc":"2.0", "method": "state_call", "params": ["DexApi_quote_price_tokens_for_exact_tokens", "0x0101000000000000000000000011000000000000000000"]}' \
//! http://localhost:9933/
//! ```

#![cfg_attr(not(feature = "std"), no_std)]
use frame_support::traits::Incrementable;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;

mod types;
pub mod weights;

#[cfg(test)]
mod tests;

#[cfg(test)]
mod mock;

use codec::Codec;
use frame_support::{
	ensure,
	traits::tokens::{AssetId, Balance},
};
use frame_system::{ensure_signed, pallet_prelude::OriginFor};
pub use pallet::*;
use sp_arithmetic::traits::Unsigned;
use sp_runtime::{
	traits::{CheckedAdd, CheckedDiv, CheckedMul, CheckedSub, Ensure, MaybeDisplay, Zero},
	DispatchError,
};
pub use types::*;
pub use weights::WeightInfo;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::{
		pallet_prelude::*,
		traits::{
			fungible::{Inspect as InspectFungible, Mutate as MutateFungible},
			fungibles::{Create, Inspect, Mutate},
			tokens::{
				Fortitude::Polite,
				Precision::Exact,
				Preservation::{Expendable, Preserve},
			},
		},
		PalletId,
	};
	use sp_runtime::{
		traits::{AccountIdConversion, IntegerSquareRoot, One, Zero},
		Saturating,
	};
	use sp_std::prelude::*;

	#[pallet::pallet]
	pub struct Pallet<T>(PhantomData<T>);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// Overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// Currency type that this works on.
		type Currency: InspectFungible<Self::AccountId, Balance = Self::Balance>
			+ MutateFungible<Self::AccountId>;

		/// The `Currency::Balance` type.
		type Balance: Balance;

		/// The type used to describe the amount of fractions converted into assets.
		type AssetBalance: Balance;

		type HigherPrecisionBalance: IntegerSquareRoot
			+ One
			+ Ensure
			+ Unsigned
			+ From<u32>
			+ From<Self::AssetBalance>
			+ From<Self::Balance>
			+ TryInto<Self::AssetBalance>
			+ TryInto<Self::Balance>;

		/// Identifier for the class of asset.
		type AssetId: AssetId + PartialOrd;

		/// Type that holds both Native currency and token from `Assets`.
		type MultiAssetId: AssetId + PartialOrd;

		/// Type to convert `AssetId` into `MultiAssetId`.
		type MultiAssetIdConverter: MultiAssetIdConverter<Self::MultiAssetId, Self::AssetId>;

		/// Asset id to address the lp tokens by.
		type PoolAssetId: AssetId + PartialOrd + Incrementable + From<u32>;

		/// Registry for the assets.
		type Assets: Inspect<Self::AccountId, AssetId = Self::AssetId, Balance = Self::AssetBalance>
			+ Mutate<Self::AccountId>;

		/// Registry for the lp tokens. Ideally only this pallet should have create permissions on
		/// the assets.
		type PoolAssets: Inspect<Self::AccountId, AssetId = Self::PoolAssetId, Balance = Self::AssetBalance>
			+ Create<Self::AccountId>
			+ Mutate<Self::AccountId>;

		/// A % the liquidity providers will take of every swap. Represents 10ths of a percent.
		type LPFee: Get<u32>;

		/// A one-time fee to setup the pool.
		type PoolSetupFee: Get<Self::Balance>;

		/// An account that receives the pool setup fee.
		type PoolSetupFeeReceiver: Get<Self::AccountId>;

		/// The minimum LP token amount that could be minted. Ameliorates rounding errors.
		type MintMinLiquidity: Get<Self::AssetBalance>;

		/// The max number of hops in a swap.
		#[pallet::constant]
		type MaxSwapPathLength: Get<u32>;

		/// The dex's pallet id, used for deriving its sovereign account ID.
		#[pallet::constant]
		type PalletId: Get<PalletId>;

		/// A setting to allow creating pools with both non-native assets.
		#[pallet::constant]
		type AllowMultiAssetPools: Get<bool>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
	}

	#[pallet::storage]
	pub type Pools<T: Config> =
		StorageMap<_, Blake2_128Concat, PoolIdOf<T>, PoolInfo<T::PoolAssetId>, OptionQuery>;

	/// Stores the `PoolAssetId` that is going to be used for the next lp token.
	/// This gets incremented whenever a new lp pool is created.
	#[pallet::storage]
	pub type NextPoolAssetId<T: Config> = StorageValue<_, T::PoolAssetId, OptionQuery>;

	// Pallet's events.
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		PoolCreated {
			creator: T::AccountId,
			pool_id: PoolIdOf<T>,
			lp_token: T::PoolAssetId,
		},
		LiquidityAdded {
			who: T::AccountId,
			mint_to: T::AccountId,
			pool_id: PoolIdOf<T>,
			amount1_provided: AssetBalanceOf<T>,
			amount2_provided: AssetBalanceOf<T>,
			lp_token: T::PoolAssetId,
			lp_token_minted: AssetBalanceOf<T>,
		},
		LiquidityRemoved {
			who: T::AccountId,
			withdraw_to: T::AccountId,
			pool_id: PoolIdOf<T>,
			amount1: AssetBalanceOf<T>,
			amount2: AssetBalanceOf<T>,
			lp_token: T::PoolAssetId,
			lp_token_burned: AssetBalanceOf<T>,
		},
		SwapExecuted {
			who: T::AccountId,
			send_to: T::AccountId,
			path: BoundedVec<T::MultiAssetId, T::MaxSwapPathLength>,
			amount_in: AssetBalanceOf<T>,
			amount_out: AssetBalanceOf<T>,
		},
		Transfer {
			from: T::AccountId,
			to: T::AccountId,
			asset: T::MultiAssetId,
			amount: AssetBalanceOf<T>,
		},
	}

	// Your Pallet's error messages.
	#[pallet::error]
	pub enum Error<T> {
		/// Provided assets are equal.
		EqualAssets,
		/// Pool already exists.
		PoolExists,
		/// Desired amount can't be zero.
		WrongDesiredAmount,
		/// Provided amount should be greater or equal to existential deposit.
		AmountLessThanED,
		/// Desired amount can't be equal to the pool reserve.
		AmountOutTooHigh,
		/// The pool doesn't exist.
		PoolNotFound,
		/// An overflow happened.
		Overflow,
		/// The minimal amount requirement for the first token in the pair wasn't met.
		AssetOneDepositDidNotMeetMinimum,
		/// The minimal amount requirement for the second token in the pair wasn't met.
		AssetTwoDepositDidNotMeetMinimum,
		/// The minimal amount requirement for the first token in the pair wasn't met.
		AssetOneWithdrawalDidNotMeetMinimum,
		/// The minimal amount requirement for the second token in the pair wasn't met.
		AssetTwoWithdrawalDidNotMeetMinimum,
		/// Optimal calculated amount is less than desired.
		OptimalAmountLessThanDesired,
		/// Insufficient liquidity minted.
		InsufficientLiquidityMinted,
		/// Asked liquidity can't be zero.
		ZeroLiquidity,
		/// Amount can't be zero.
		ZeroAmount,
		/// Insufficient liquidity in the pool.
		InsufficientLiquidity,
		/// Calculated amount out is less than provided minimum amount.
		ProvidedMinimumNotSufficientForSwap,
		/// Provided maximum amount is not sufficient for swap.
		ProvidedMaximumNotSufficientForSwap,
		/// Only pools with native on one side are valid.
		PoolMustContainNativeCurrency,
		/// The provided path must consists of 2 assets at least.
		InvalidPath,
		/// It was not possible to calculate path data.
		PathError,
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<T::BlockNumber> for Pallet<T>
	where
		T::AssetId: From<u32>,
	{
		fn integrity_test() {
			sp_std::if_std! {
				sp_io::TestExternalities::new_empty().execute_with(|| {
					// ensure that the `AccountId` is set properly and doesn't generate the same
					// pool account for different pool ids.
					let native = T::MultiAssetIdConverter::get_native();
					let asset_1 = T::MultiAssetIdConverter::into_multiasset_id(1.into());
					let asset_2 = T::MultiAssetIdConverter::into_multiasset_id(2.into());
					let pool_account_1 = Self::get_pool_account((native, asset_1));
					let pool_account_2 = Self::get_pool_account((native, asset_2));
					assert!(
						pool_account_1 != pool_account_2,
						"AccountId should be set at least to u128"
					);
				});
			}
		}
	}

	// Pallet's callable functions.
	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Creates an empty liquidity pool and an associated new `lp_token` asset
		/// (the id of which is returned in the `Event::PoolCreated` event).
		#[pallet::call_index(0)]
		#[pallet::weight(T::WeightInfo::create_pool())]
		pub fn create_pool(
			origin: OriginFor<T>,
			asset1: T::MultiAssetId,
			asset2: T::MultiAssetId,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			ensure!(asset1 != asset2, Error::<T>::EqualAssets);

			let pool_id = Self::get_pool_id(asset1, asset2);
			let (asset1, _asset2) = pool_id;

			if !T::AllowMultiAssetPools::get() && T::MultiAssetIdConverter::get_native() != asset1 {
				Err(Error::<T>::PoolMustContainNativeCurrency)?;
			}

			ensure!(!Pools::<T>::contains_key(&pool_id), Error::<T>::PoolExists);

			let pool_account = Self::get_pool_account(pool_id);
			frame_system::Pallet::<T>::inc_providers(&pool_account);

			// pay the setup fee
			T::Currency::transfer(
				&sender,
				&T::PoolSetupFeeReceiver::get(),
				T::PoolSetupFee::get(),
				Preserve,
			)?;

			let lp_token = NextPoolAssetId::<T>::get().unwrap_or(T::PoolAssetId::initial_value());
			let next_lp_token_id = lp_token.increment();
			NextPoolAssetId::<T>::set(Some(next_lp_token_id));

			T::PoolAssets::create(lp_token, pool_account.clone(), false, 1u32.into())?;

			let pool_info = PoolInfo { lp_token };
			Pools::<T>::insert(pool_id, pool_info);

			Self::deposit_event(Event::PoolCreated { creator: sender, pool_id, lp_token });

			Ok(())
		}

		/// Provide liquidity into the pool of `asset1` and `asset2`.
		/// NOTE: an optimal amount of asset1 and asset2 will be calculated and
		/// might be different to provided `amount1_desired`/`amount2_desired`
		/// thus it's needed to provide the min amount you're happy to provide.
		/// Params `amount1_min`/`amount2_min` represent that.
		/// `mint_to` will be sent the liquidity tokens that represent this share of the pool.
		#[pallet::call_index(1)]
		#[pallet::weight(T::WeightInfo::add_liquidity())]
		pub fn add_liquidity(
			origin: OriginFor<T>,
			asset1: T::MultiAssetId,
			asset2: T::MultiAssetId,
			amount1_desired: AssetBalanceOf<T>,
			amount2_desired: AssetBalanceOf<T>,
			amount1_min: AssetBalanceOf<T>,
			amount2_min: AssetBalanceOf<T>,
			mint_to: T::AccountId,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			let pool_id = Self::get_pool_id(asset1, asset2);
			let (asset1, asset2) = pool_id;

			ensure!(
				amount1_desired > Zero::zero() && amount2_desired > Zero::zero(),
				Error::<T>::WrongDesiredAmount
			);

			let maybe_pool = Pools::<T>::get(pool_id);
			let pool = maybe_pool.as_ref().ok_or(Error::<T>::PoolNotFound)?;

			let amount1: AssetBalanceOf<T>;
			let amount2: AssetBalanceOf<T>;

			let pool_account = Self::get_pool_account(pool_id);
			let reserve1 = Self::get_balance(&pool_account, asset1)?;
			let reserve2 = Self::get_balance(&pool_account, asset2)?;

			if reserve1.is_zero() && reserve2.is_zero() {
				if T::MultiAssetIdConverter::get_native() == asset1 {
					ensure!(
						T::HigherPrecisionBalance::from(amount1_desired) >=
							T::HigherPrecisionBalance::from(T::Currency::minimum_balance()),
						Error::<T>::AmountLessThanED
					);
				}
				amount1 = amount1_desired;
				amount2 = amount2_desired;
			} else {
				let amount2_optimal = Self::quote(&amount1_desired, &reserve1, &reserve2)?;

				if amount2_optimal <= amount2_desired {
					ensure!(
						amount2_optimal >= amount2_min,
						Error::<T>::AssetTwoDepositDidNotMeetMinimum
					);
					amount1 = amount1_desired;
					amount2 = amount2_optimal;
				} else {
					let amount1_optimal = Self::quote(&amount2_desired, &reserve2, &reserve1)?;
					ensure!(
						amount1_optimal <= amount1_desired,
						Error::<T>::OptimalAmountLessThanDesired
					);
					ensure!(
						amount1_optimal >= amount1_min,
						Error::<T>::AssetOneDepositDidNotMeetMinimum
					);
					amount1 = amount1_optimal;
					amount2 = amount2_desired;
				}
			}

			Self::transfer(asset1, &sender, &pool_account, amount1, true)?;
			Self::transfer(asset2, &sender, &pool_account, amount2, true)?;

			let total_supply = T::PoolAssets::total_issuance(pool.lp_token);

			let lp_token_amount: AssetBalanceOf<T>;
			if total_supply.is_zero() {
				lp_token_amount = Self::calc_lp_amount_for_zero_supply(&amount1, &amount2)?;
				T::PoolAssets::mint_into(pool.lp_token, &pool_account, T::MintMinLiquidity::get())?;
			} else {
				let side1 = Self::mul_div(&amount1, &total_supply, &reserve1)?;
				let side2 = Self::mul_div(&amount2, &total_supply, &reserve2)?;
				lp_token_amount = side1.min(side2);
			}

			ensure!(
				lp_token_amount > T::MintMinLiquidity::get(),
				Error::<T>::InsufficientLiquidityMinted
			);

			T::PoolAssets::mint_into(pool.lp_token, &mint_to, lp_token_amount)?;

			Self::deposit_event(Event::LiquidityAdded {
				who: sender,
				mint_to,
				pool_id,
				amount1_provided: amount1,
				amount2_provided: amount2,
				lp_token: pool.lp_token,
				lp_token_minted: lp_token_amount,
			});

			Ok(())
		}

		/// Allows to remove the liquidity by providing an lp token.
		/// With the usage of `amount1_min`/`amount2_min` it's possible to control
		/// the min amount of returned tokens you're happy with.
		#[pallet::call_index(2)]
		#[pallet::weight(T::WeightInfo::remove_liquidity())]
		pub fn remove_liquidity(
			origin: OriginFor<T>,
			asset1: T::MultiAssetId,
			asset2: T::MultiAssetId,
			lp_token_burn: AssetBalanceOf<T>,
			amount1_min_receive: AssetBalanceOf<T>,
			amount2_min_receive: AssetBalanceOf<T>,
			withdraw_to: T::AccountId,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			let pool_id = Self::get_pool_id(asset1, asset2);
			let (asset1, asset2) = pool_id;

			ensure!(lp_token_burn > Zero::zero(), Error::<T>::ZeroLiquidity);

			let maybe_pool = Pools::<T>::get(pool_id);
			let pool = maybe_pool.as_ref().ok_or(Error::<T>::PoolNotFound)?;

			let pool_account = Self::get_pool_account(pool_id);
			let reserve1 = Self::get_balance(&pool_account, asset1)?;
			let reserve2 = Self::get_balance(&pool_account, asset2)?;

			let total_supply = T::PoolAssets::total_issuance(pool.lp_token);

			let amount1 = Self::mul_div(&lp_token_burn, &reserve1, &total_supply)?;
			let amount2 = Self::mul_div(&lp_token_burn, &reserve2, &total_supply)?;

			ensure!(
				!amount1.is_zero() && amount1 >= amount1_min_receive,
				Error::<T>::AssetOneWithdrawalDidNotMeetMinimum
			);
			ensure!(
				!amount2.is_zero() && amount2 >= amount2_min_receive,
				Error::<T>::AssetTwoWithdrawalDidNotMeetMinimum
			);

			T::PoolAssets::burn_from(pool.lp_token, &sender, lp_token_burn, Exact, Polite)?;

			Self::transfer(asset1, &pool_account, &withdraw_to, amount1, false)?;
			Self::transfer(asset2, &pool_account, &withdraw_to, amount2, false)?;

			Self::deposit_event(Event::LiquidityRemoved {
				who: sender,
				withdraw_to,
				pool_id,
				amount1,
				amount2,
				lp_token: pool.lp_token,
				lp_token_burned: lp_token_burn,
			});

			Ok(())
		}

		/// Swap the exact amount of `asset1` into `asset2`.
		/// `amount_out_min` param allows to specify the min amount of the `asset2`
		/// you're happy to receive.
		#[pallet::call_index(3)]
		#[pallet::weight(T::WeightInfo::swap_exact_tokens_for_tokens())]
		pub fn swap_exact_tokens_for_tokens(
			origin: OriginFor<T>,
			path: BoundedVec<T::MultiAssetId, T::MaxSwapPathLength>,
			amount_in: AssetBalanceOf<T>,
			amount_out_min: AssetBalanceOf<T>,
			send_to: T::AccountId,
			keep_alive: bool,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			ensure!(
				amount_in > Zero::zero() && amount_out_min > Zero::zero(),
				Error::<T>::ZeroAmount
			);
			ensure!(path.len() >= 2, Error::<T>::InvalidPath);

			let amounts = Self::get_amounts_out(&amount_in, &path)?;
			let amount_out = *amounts.last().expect("Has always more than 1 element");
			ensure!(amount_out >= amount_out_min, Error::<T>::ProvidedMinimumNotSufficientForSwap);

			Self::do_swap(&sender, &amounts, &path, &send_to, keep_alive)?;

			Self::deposit_event(Event::SwapExecuted {
				who: sender,
				send_to,
				path,
				amount_in,
				amount_out,
			});

			Ok(())
		}

		/// Swap any amount of `asset1` to get the exact amount of `asset2`.
		/// `amount_in_max` param allows to specify the max amount of the `asset1`
		/// you're happy to provide.
		#[pallet::call_index(4)]
		#[pallet::weight(T::WeightInfo::swap_tokens_for_exact_tokens())]
		pub fn swap_tokens_for_exact_tokens(
			origin: OriginFor<T>,
			path: BoundedVec<T::MultiAssetId, T::MaxSwapPathLength>,
			amount_out: AssetBalanceOf<T>,
			amount_in_max: AssetBalanceOf<T>,
			send_to: T::AccountId,
			keep_alive: bool,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			ensure!(
				amount_out > Zero::zero() && amount_in_max > Zero::zero(),
				Error::<T>::ZeroAmount
			);
			ensure!(path.len() >= 2, Error::<T>::InvalidPath);

			let amounts = Self::get_amounts_in(&amount_out, &path)?;
			let amount_in = *amounts.first().expect("Always has more than one element");
			ensure!(amount_in <= amount_in_max, Error::<T>::ProvidedMaximumNotSufficientForSwap);

			Self::do_swap(&sender, &amounts, &path, &send_to, keep_alive)?;

			Self::deposit_event(Event::SwapExecuted {
				who: sender,
				send_to,
				path,
				amount_in,
				amount_out,
			});

			Ok(())
		}
	}

	impl<T: Config> Pallet<T> {
		fn transfer(
			asset_id: T::MultiAssetId,
			from: &T::AccountId,
			to: &T::AccountId,
			amount: AssetBalanceOf<T>,
			keep_alive: bool,
		) -> Result<T::AssetBalance, DispatchError> {
			Self::deposit_event(Event::Transfer {
				from: from.clone(),
				to: to.clone(),
				asset: asset_id,
				amount,
			});
			if T::MultiAssetIdConverter::get_native() == asset_id {
				let preservation = match keep_alive {
					true => Preserve,
					false => Expendable,
				};
				let amount = Self::asset_to_native(amount)?;
				Ok(Self::native_to_asset(T::Currency::transfer(from, to, amount, preservation)?)?)
			} else {
				T::Assets::transfer(
					T::MultiAssetIdConverter::try_convert(asset_id)
						.map_err(|_| Error::<T>::Overflow)?,
					from,
					to,
					amount,
					Expendable,
				)
			}
		}

		pub(crate) fn native_to_asset(amount: T::Balance) -> Result<T::AssetBalance, Error<T>> {
			T::HigherPrecisionBalance::from(amount)
				.try_into()
				.map_err(|_| Error::<T>::Overflow)
		}

		pub(crate) fn asset_to_native(amount: T::AssetBalance) -> Result<T::Balance, Error<T>> {
			T::HigherPrecisionBalance::from(amount)
				.try_into()
				.map_err(|_| Error::<T>::Overflow)
		}

		pub(crate) fn do_swap(
			sender: &T::AccountId,
			amounts: &Vec<AssetBalanceOf<T>>,
			path: &BoundedVec<T::MultiAssetId, T::MaxSwapPathLength>,
			send_to: &T::AccountId,
			keep_alive: bool,
		) -> Result<(), DispatchError> {
			if let Some(&[asset1, asset2]) = path.get(0..2) {
				let pool_id = Self::get_pool_id(asset1, asset2);
				let pool_account = Self::get_pool_account(pool_id);
				let first_amount = amounts.first().expect("Always has more than one element");

				Self::transfer(asset1, sender, &pool_account, *first_amount, keep_alive)?;

				let mut i = 0;
				let path_len = path.len() as u32;
				for assets_pair in path.windows(2) {
					if let &[asset1, asset2] = assets_pair {
						let pool_id = Self::get_pool_id(asset1, asset2);
						let pool_account = Self::get_pool_account(pool_id);

						let amount_out =
							amounts.get((i + 1) as usize).ok_or(Error::<T>::PathError)?;

						let to = if i < path_len - 2 {
							let asset3 = path.get((i + 2) as usize).ok_or(Error::<T>::PathError)?;
							Self::get_pool_account(Self::get_pool_id(asset2, *asset3))
						} else {
							send_to.clone()
						};

						Self::transfer(asset2, &pool_account, &to, *amount_out, true)?;
					}
					i.saturating_inc();
				}
			}
			Ok(())
		}

		/// The account ID of the pool.
		///
		/// This actually does computation. If you need to keep using it, then make sure you cache
		/// the value and only call this once.
		pub fn get_pool_account(pool_id: PoolIdOf<T>) -> T::AccountId {
			T::PalletId::get().into_sub_account_truncating(pool_id)
		}

		fn get_balance(
			owner: &T::AccountId,
			token_id: T::MultiAssetId,
		) -> Result<T::AssetBalance, Error<T>> {
			if T::MultiAssetIdConverter::get_native() == token_id {
				Self::native_to_asset(<<T as Config>::Currency>::reducible_balance(
					owner, Expendable, Polite,
				))
			} else {
				Ok(<<T as Config>::Assets>::reducible_balance(
					T::MultiAssetIdConverter::try_convert(token_id)
						.map_err(|_| Error::<T>::Overflow)?,
					owner,
					Expendable,
					Polite,
				))
			}
		}

		/// Returns a pool id constructed from 2 sorted assets.
		/// Native asset should be lower than the other asset ids.
		pub fn get_pool_id(asset1: T::MultiAssetId, asset2: T::MultiAssetId) -> PoolIdOf<T> {
			if asset1 <= asset2 {
				(asset1, asset2)
			} else {
				(asset2, asset1)
			}
		}

		pub fn get_reserves(
			asset1: T::MultiAssetId,
			asset2: T::MultiAssetId,
		) -> Result<(AssetBalanceOf<T>, AssetBalanceOf<T>), Error<T>> {
			let pool_id = Self::get_pool_id(asset1, asset2);
			let pool_account = Self::get_pool_account(pool_id);

			let balance1 = Self::get_balance(&pool_account, asset1)?;
			let balance2 = Self::get_balance(&pool_account, asset2)?;

			if balance1.is_zero() || balance2.is_zero() {
				Err(Error::<T>::PoolNotFound)?;
			}

			Ok((balance1, balance2))
		}

		pub(crate) fn get_amounts_in(
			amount_out: &AssetBalanceOf<T>,
			path: &BoundedVec<T::MultiAssetId, T::MaxSwapPathLength>,
		) -> Result<Vec<AssetBalanceOf<T>>, DispatchError> {
			let mut amounts: Vec<AssetBalanceOf<T>> = vec![*amount_out];

			for assets_pair in path.windows(2).rev() {
				if let &[asset1, asset2] = assets_pair {
					let (reserve_in, reserve_out) = Self::get_reserves(asset1, asset2)?;
					let prev_amount = amounts.last().expect("Always has at least one element");
					let amount_in = Self::get_amount_in(prev_amount, &reserve_in, &reserve_out)?;
					amounts.push(amount_in);
				}
			}

			amounts.reverse();
			Ok(amounts)
		}

		pub(crate) fn get_amounts_out(
			amount_in: &AssetBalanceOf<T>,
			path: &BoundedVec<T::MultiAssetId, T::MaxSwapPathLength>,
		) -> Result<Vec<AssetBalanceOf<T>>, DispatchError> {
			let mut amounts: Vec<AssetBalanceOf<T>> = vec![*amount_in];

			for assets_pair in path.windows(2) {
				if let &[asset1, asset2] = assets_pair {
					let (reserve_in, reserve_out) = Self::get_reserves(asset1, asset2)?;
					let prev_amount = amounts.last().expect("Always has at least one element");
					let amount_out = Self::get_amount_out(prev_amount, &reserve_in, &reserve_out)?;
					amounts.push(amount_out);
				}
			}

			Ok(amounts)
		}

		/// Used by the RPC service to provide current prices.
		pub fn quote_price_exact_tokens_for_tokens(
			asset1: T::MultiAssetId,
			asset2: T::MultiAssetId,
			amount: AssetBalanceOf<T>,
			include_fee: bool,
		) -> Option<AssetBalanceOf<T>> {
			let pool_id = Self::get_pool_id(asset1, asset2);
			let pool_account = Self::get_pool_account(pool_id);

			let balance1 = Self::get_balance(&pool_account, asset1).ok()?;
			let balance2 = Self::get_balance(&pool_account, asset2).ok()?;
			if !balance1.is_zero() {
				if include_fee {
					Self::get_amount_out(&amount, &balance1, &balance2).ok()
				} else {
					Self::quote(&amount, &balance1, &balance2).ok()
				}
			} else {
				None
			}
		}

		/// Used by the RPC service to provide current prices.
		pub fn quote_price_tokens_for_exact_tokens(
			asset1: T::MultiAssetId,
			asset2: T::MultiAssetId,
			amount: AssetBalanceOf<T>,
			include_fee: bool,
		) -> Option<AssetBalanceOf<T>> {
			let pool_id = Self::get_pool_id(asset1, asset2);
			let pool_account = Self::get_pool_account(pool_id);

			let balance1 = Self::get_balance(&pool_account, asset1).ok()?;
			let balance2 = Self::get_balance(&pool_account, asset2).ok()?;
			if !balance1.is_zero() {
				if include_fee {
					Self::get_amount_in(&amount, &balance1, &balance2).ok()
				} else {
					Self::quote(&amount, &balance1, &balance2).ok()
				}
			} else {
				None
			}
		}

		/// Calculates the optimal amount from the reserves.
		pub fn quote(
			amount: &AssetBalanceOf<T>,
			reserve1: &AssetBalanceOf<T>,
			reserve2: &AssetBalanceOf<T>,
		) -> Result<AssetBalanceOf<T>, Error<T>> {
			// amount * reserve2 / reserve1
			Self::mul_div(amount, reserve2, reserve1)
		}

		pub(super) fn calc_lp_amount_for_zero_supply(
			amount1: &AssetBalanceOf<T>,
			amount2: &AssetBalanceOf<T>,
		) -> Result<AssetBalanceOf<T>, Error<T>> {
			let amount1 = T::HigherPrecisionBalance::from(*amount1);
			let amount2 = T::HigherPrecisionBalance::from(*amount2);

			let result = amount1
				.checked_mul(&amount2)
				.ok_or(Error::<T>::Overflow)?
				.integer_sqrt()
				.checked_sub(&T::MintMinLiquidity::get().into())
				.ok_or(Error::<T>::InsufficientLiquidityMinted)?;

			result.try_into().map_err(|_| Error::<T>::Overflow)
		}

		fn mul_div(
			a: &AssetBalanceOf<T>,
			b: &AssetBalanceOf<T>,
			c: &AssetBalanceOf<T>,
		) -> Result<AssetBalanceOf<T>, Error<T>> {
			let a = T::HigherPrecisionBalance::from(*a);
			let b = T::HigherPrecisionBalance::from(*b);
			let c = T::HigherPrecisionBalance::from(*c);

			let result = a
				.checked_mul(&b)
				.ok_or(Error::<T>::Overflow)?
				.checked_div(&c)
				.ok_or(Error::<T>::Overflow)?;

			result.try_into().map_err(|_| Error::<T>::Overflow)
		}

		/// Calculates amount out
		///
		/// Given an input amount of an asset and pair reserves, returns the maximum output amount
		/// of the other asset
		pub fn get_amount_out(
			amount_in: &AssetBalanceOf<T>,
			reserve_in: &AssetBalanceOf<T>,
			reserve_out: &AssetBalanceOf<T>,
		) -> Result<AssetBalanceOf<T>, Error<T>> {
			let amount_in = T::HigherPrecisionBalance::from(*amount_in);
			let reserve_in = T::HigherPrecisionBalance::from(*reserve_in);
			let reserve_out = T::HigherPrecisionBalance::from(*reserve_out);

			if reserve_in.is_zero() || reserve_out.is_zero() {
				return Err(Error::<T>::ZeroLiquidity.into())
			}

			let amount_in_with_fee = amount_in
				.checked_mul(&(T::HigherPrecisionBalance::from(1000u32) - (T::LPFee::get().into())))
				.ok_or(Error::<T>::Overflow)?;

			let numerator =
				amount_in_with_fee.checked_mul(&reserve_out).ok_or(Error::<T>::Overflow)?;

			let denominator = reserve_in
				.checked_mul(&1000u32.into())
				.ok_or(Error::<T>::Overflow)?
				.checked_add(&amount_in_with_fee)
				.ok_or(Error::<T>::Overflow)?;

			let result = numerator.checked_div(&denominator).ok_or(Error::<T>::Overflow)?;

			result.try_into().map_err(|_| Error::<T>::Overflow)
		}

		/// Calculates amount in
		///
		/// Given an output amount of an asset and pair reserves, returns a required input amount
		/// of the other asset
		pub fn get_amount_in(
			amount_out: &AssetBalanceOf<T>,
			reserve_in: &AssetBalanceOf<T>,
			reserve_out: &AssetBalanceOf<T>,
		) -> Result<AssetBalanceOf<T>, Error<T>> {
			let amount_out = T::HigherPrecisionBalance::from(*amount_out);
			let reserve_in = T::HigherPrecisionBalance::from(*reserve_in);
			let reserve_out = T::HigherPrecisionBalance::from(*reserve_out);

			if reserve_in.is_zero() || reserve_out.is_zero() {
				Err(Error::<T>::ZeroLiquidity.into())?
			}

			if amount_out == reserve_out {
				Err(Error::<T>::AmountOutTooHigh.into())?
			}

			let numerator = reserve_in
				.checked_mul(&amount_out)
				.ok_or(Error::<T>::Overflow)?
				.checked_mul(&1000u32.into())
				.ok_or(Error::<T>::Overflow)?;

			let denominator = reserve_out
				.checked_sub(&amount_out)
				.ok_or(Error::<T>::Overflow)?
				.checked_mul(&(T::HigherPrecisionBalance::from(1000u32) - T::LPFee::get().into()))
				.ok_or(Error::<T>::Overflow)?;

			let result = numerator
				.checked_div(&denominator)
				.ok_or(Error::<T>::Overflow)?
				.checked_add(&One::one())
				.ok_or(Error::<T>::Overflow)?;

			result.try_into().map_err(|_| Error::<T>::Overflow)
		}

		#[cfg(any(test, feature = "runtime-benchmarks"))]
		pub fn get_next_pool_asset_id() -> T::PoolAssetId {
			NextPoolAssetId::<T>::get().unwrap_or(T::PoolAssetId::initial_value())
		}
	}
}

impl<T: Config>
	frame_support::traits::tokens::fungibles::SwapForNative<
		T::RuntimeOrigin,
		T::AccountId,
		T::Balance,
		T::AssetBalance,
		T::AssetId,
	> for Pallet<T>
where
	<T as pallet::Config>::Currency:
		frame_support::traits::Currency<<T as frame_system::Config>::AccountId>,
{
	// If successful returns the amount in.
	fn swap_tokens_for_exact_native(
		sender: T::AccountId,
		asset_id: T::AssetId,
		amount_out: T::Balance,
		amount_in_max: Option<T::AssetBalance>,
		send_to: T::AccountId,
		keep_alive: bool,
	) -> Result<T::AssetBalance, DispatchError> {
		ensure!(amount_out > Zero::zero(), Error::<T>::ZeroAmount);
		if let Some(amount_in_max) = amount_in_max {
			ensure!(amount_in_max > Zero::zero(), Error::<T>::ZeroAmount);
		}
		let mut path = sp_std::vec::Vec::new();
		path.push(T::MultiAssetIdConverter::into_multiasset_id(asset_id));
		path.push(T::MultiAssetIdConverter::get_native());
		let path = path.try_into().unwrap();

		let amount_out = Self::native_to_asset(amount_out)?;

		let amounts = Self::get_amounts_in(&amount_out, &path)?;
		let amount_in = *amounts.first().expect("Always has more than one element");
		if let Some(amount_in_max) = amount_in_max {
			ensure!(amount_in <= amount_in_max, Error::<T>::ProvidedMaximumNotSufficientForSwap);
		}

		Self::do_swap(&sender, &amounts, &path, &send_to, keep_alive)?;

		Self::deposit_event(Event::SwapExecuted {
			who: sender,
			send_to,
			path,
			amount_in,
			amount_out,
		});

		Ok(amount_in)
	}
}

sp_api::decl_runtime_apis! {
	pub trait DexApi<Balance, AssetBalance, AssetId> where
		Balance: Codec + MaybeDisplay,
		AssetBalance: frame_support::traits::tokens::Balance,
		AssetId: Codec + MaybeDisplay
	{
		fn quote_price_tokens_for_exact_tokens(asset1: AssetId, asset2: AssetId, amount: AssetBalance, include_fee: bool) -> Option<Balance>;

		fn quote_price_exact_tokens_for_tokens(asset1: AssetId, asset2: AssetId, amount: AssetBalance, include_fee: bool) -> Option<Balance>;

		fn get_reserves(asset1: AssetId, asset2: AssetId) -> Option<(Balance, Balance)>;
	}
}
