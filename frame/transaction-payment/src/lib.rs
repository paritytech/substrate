// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! # Transaction Payment Pallet
//!
//! This pallet provides the basic logic needed to pay the absolute minimum amount needed for a
//! transaction to be included. This includes:
//!   - _base fee_: This is the minimum amount a user pays for a transaction. It is declared
//! 	as a base _weight_ in the runtime and converted to a fee using `WeightToFee`.
//!   - _weight fee_: A fee proportional to amount of weight a transaction consumes.
//!   - _length fee_: A fee proportional to the encoded length of the transaction.
//!   - _tip_: An optional tip. Tip increases the priority of the transaction, giving it a higher
//!     chance to be included by the transaction queue.
//!
//! The base fee and adjusted weight and length fees constitute the _inclusion fee_, which is
//! the minimum fee for a transaction to be included in a block.
//!
//! The formula of final fee:
//!   ```ignore
//!   inclusion_fee = base_fee + length_fee + [targeted_fee_adjustment * weight_fee];
//!   final_fee = inclusion_fee + tip;
//!   ```
//!
//!   - `targeted_fee_adjustment`: This is a multiplier that can tune the final fee based on
//! 	the congestion of the network.
//!
//! Additionally, this pallet allows one to configure:
//!   - The mapping between one unit of weight to one unit of fee via [`Config::WeightToFee`].
//!   - A means of updating the fee for the next block, via defining a multiplier, based on the
//!     final state of the chain at the end of the previous block. This can be configured via
//!     [`Config::FeeMultiplierUpdate`]
//!   - How the fees are paid via [`Config::OnChargeTransaction`].

#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Decode, Encode};
use scale_info::TypeInfo;

use sp_runtime::{
	traits::{
		Convert, DispatchInfoOf, Dispatchable, PostDispatchInfoOf, SaturatedConversion, Saturating,
		SignedExtension, Zero,
	},
	transaction_validity::{
		TransactionPriority, TransactionValidity, TransactionValidityError, ValidTransaction,
	},
	FixedPointNumber, FixedPointOperand, FixedU128, Perquintill, RuntimeDebug,
};
use sp_std::prelude::*;

use frame_support::{
	dispatch::DispatchResult,
	traits::{EstimateCallFee, Get},
	weights::{
		DispatchClass, DispatchInfo, GetDispatchInfo, Pays, PostDispatchInfo, Weight,
		WeightToFeeCoefficient, WeightToFeePolynomial,
	},
};

mod payment;
mod types;

pub use pallet::*;
pub use payment::*;
pub use types::{FeeDetails, InclusionFee, RuntimeDispatchInfo};

/// Fee multiplier.
pub type Multiplier = FixedU128;

type BalanceOf<T> = <<T as Config>::OnChargeTransaction as OnChargeTransaction<T>>::Balance;

/// A struct to update the weight multiplier per block. It implements `Convert<Multiplier,
/// Multiplier>`, meaning that it can convert the previous multiplier to the next one. This should
/// be called on `on_finalize` of a block, prior to potentially cleaning the weight data from the
/// system pallet.
///
/// given:
/// 	s = previous block weight
/// 	s'= ideal block weight
/// 	m = maximum block weight
/// 		diff = (s - s')/m
/// 		v = 0.00001
/// 		t1 = (v * diff)
/// 		t2 = (v * diff)^2 / 2
/// 	then:
/// 	next_multiplier = prev_multiplier * (1 + t1 + t2)
///
/// Where `(s', v)` must be given as the `Get` implementation of the `T` generic type. Moreover, `M`
/// must provide the minimum allowed value for the multiplier. Note that a runtime should ensure
/// with tests that the combination of this `M` and `V` is not such that the multiplier can drop to
/// zero and never recover.
///
/// note that `s'` is interpreted as a portion in the _normal transaction_ capacity of the block.
/// For example, given `s' == 0.25` and `AvailableBlockRatio = 0.75`, then the target fullness is
/// _0.25 of the normal capacity_ and _0.1875 of the entire block_.
///
/// This implementation implies the bound:
/// - `v ≤ p / k * (s − s')`
/// - or, solving for `p`: `p >= v * k * (s - s')`
///
/// where `p` is the amount of change over `k` blocks.
///
/// Hence:
/// - in a fully congested chain: `p >= v * k * (1 - s')`.
/// - in an empty chain: `p >= v * k * (-s')`.
///
/// For example, when all blocks are full and there are 28800 blocks per day (default in
/// `substrate-node`) and v == 0.00001, s' == 0.1875, we'd have:
///
/// p >= 0.00001 * 28800 * 0.8125
/// p >= 0.234
///
/// Meaning that fees can change by around ~23% per day, given extreme congestion.
///
/// More info can be found at:
/// <https://w3f-research.readthedocs.io/en/latest/polkadot/Token%20Economics.html>
pub struct TargetedFeeAdjustment<T, S, V, M>(sp_std::marker::PhantomData<(T, S, V, M)>);

/// Something that can convert the current multiplier to the next one.
pub trait MultiplierUpdate: Convert<Multiplier, Multiplier> {
	/// Minimum multiplier
	fn min() -> Multiplier;
	/// Target block saturation level
	fn target() -> Perquintill;
	/// Variability factor
	fn variability() -> Multiplier;
}

impl MultiplierUpdate for () {
	fn min() -> Multiplier {
		Default::default()
	}
	fn target() -> Perquintill {
		Default::default()
	}
	fn variability() -> Multiplier {
		Default::default()
	}
}

impl<T, S, V, M> MultiplierUpdate for TargetedFeeAdjustment<T, S, V, M>
where
	T: frame_system::Config,
	S: Get<Perquintill>,
	V: Get<Multiplier>,
	M: Get<Multiplier>,
{
	fn min() -> Multiplier {
		M::get()
	}
	fn target() -> Perquintill {
		S::get()
	}
	fn variability() -> Multiplier {
		V::get()
	}
}

impl<T, S, V, M> Convert<Multiplier, Multiplier> for TargetedFeeAdjustment<T, S, V, M>
where
	T: frame_system::Config,
	S: Get<Perquintill>,
	V: Get<Multiplier>,
	M: Get<Multiplier>,
{
	fn convert(previous: Multiplier) -> Multiplier {
		// Defensive only. The multiplier in storage should always be at most positive. Nonetheless
		// we recover here in case of errors, because any value below this would be stale and can
		// never change.
		let min_multiplier = M::get();
		let previous = previous.max(min_multiplier);

		let weights = T::BlockWeights::get();
		// the computed ratio is only among the normal class.
		let normal_max_weight = weights
			.get(DispatchClass::Normal)
			.max_total
			.unwrap_or_else(|| weights.max_block);
		let current_block_weight = <frame_system::Pallet<T>>::block_weight();
		let normal_block_weight =
			*current_block_weight.get(DispatchClass::Normal).min(&normal_max_weight);

		let s = S::get();
		let v = V::get();

		let target_weight = (s * normal_max_weight) as u128;
		let block_weight = normal_block_weight as u128;

		// determines if the first_term is positive
		let positive = block_weight >= target_weight;
		let diff_abs = block_weight.max(target_weight) - block_weight.min(target_weight);

		// defensive only, a test case assures that the maximum weight diff can fit in Multiplier
		// without any saturation.
		let diff = Multiplier::saturating_from_rational(diff_abs, normal_max_weight.max(1));
		let diff_squared = diff.saturating_mul(diff);

		let v_squared_2 = v.saturating_mul(v) / Multiplier::saturating_from_integer(2);

		let first_term = v.saturating_mul(diff);
		let second_term = v_squared_2.saturating_mul(diff_squared);

		if positive {
			let excess = first_term.saturating_add(second_term).saturating_mul(previous);
			previous.saturating_add(excess).max(min_multiplier)
		} else {
			// Defensive-only: first_term > second_term. Safe subtraction.
			let negative = first_term.saturating_sub(second_term).saturating_mul(previous);
			previous.saturating_sub(negative).max(min_multiplier)
		}
	}
}

/// Storage releases of the pallet.
#[derive(Encode, Decode, Clone, Copy, PartialEq, Eq, RuntimeDebug, TypeInfo)]
enum Releases {
	/// Original version of the pallet.
	V1Ancient,
	/// One that bumps the usage to FixedU128 from FixedI128.
	V2,
}

impl Default for Releases {
	fn default() -> Self {
		Releases::V1Ancient
	}
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// Handler for withdrawing, refunding and depositing the transaction fee.
		/// Transaction fees are withdrawn before the transaction is executed.
		/// After the transaction was executed the transaction weight can be
		/// adjusted, depending on the used resources by the transaction. If the
		/// transaction weight is lower than expected, parts of the transaction fee
		/// might be refunded. In the end the fees can be deposited.
		type OnChargeTransaction: OnChargeTransaction<Self>;

		/// The fee to be paid for making a transaction; the per-byte portion.
		#[pallet::constant]
		type TransactionByteFee: Get<BalanceOf<Self>>;

		/// A fee mulitplier for `Operational` extrinsics to compute "virtual tip" to boost their
		/// `priority`
		///
		/// This value is multipled by the `final_fee` to obtain a "virtual tip" that is later
		/// added to a tip component in regular `priority` calculations.
		/// It means that a `Normal` transaction can front-run a similarly-sized `Operational`
		/// extrinsic (with no tip), by including a tip value greater than the virtual tip.
		///
		/// ```rust,ignore
		/// // For `Normal`
		/// let priority = priority_calc(tip);
		///
		/// // For `Operational`
		/// let virtual_tip = (inclusion_fee + tip) * OperationalFeeMultiplier;
		/// let priority = priority_calc(tip + virtual_tip);
		/// ```
		///
		/// Note that since we use `final_fee` the multiplier applies also to the regular `tip`
		/// sent with the transaction. So, not only does the transaction get a priority bump based
		/// on the `inclusion_fee`, but we also amplify the impact of tips applied to `Operational`
		/// transactions.
		#[pallet::constant]
		type OperationalFeeMultiplier: Get<u8>;

		/// Convert a weight value into a deductible fee based on the currency type.
		type WeightToFee: WeightToFeePolynomial<Balance = BalanceOf<Self>>;

		/// Update the multiplier of the next block, based on the previous block's weight.
		type FeeMultiplierUpdate: MultiplierUpdate;
	}

	#[pallet::extra_constants]
	impl<T: Config> Pallet<T> {
		// TODO: rename to snake case after https://github.com/paritytech/substrate/issues/8826 fixed.
		#[allow(non_snake_case)]
		/// The polynomial that is applied in order to derive fee from weight.
		fn WeightToFee() -> Vec<WeightToFeeCoefficient<BalanceOf<T>>> {
			T::WeightToFee::polynomial().to_vec()
		}
	}

	#[pallet::type_value]
	pub fn NextFeeMultiplierOnEmpty() -> Multiplier {
		Multiplier::saturating_from_integer(1)
	}

	#[pallet::storage]
	#[pallet::getter(fn next_fee_multiplier)]
	pub type NextFeeMultiplier<T: Config> =
		StorageValue<_, Multiplier, ValueQuery, NextFeeMultiplierOnEmpty>;

	#[pallet::storage]
	pub(super) type StorageVersion<T: Config> = StorageValue<_, Releases, ValueQuery>;

	#[pallet::genesis_config]
	pub struct GenesisConfig;

	#[cfg(feature = "std")]
	impl Default for GenesisConfig {
		fn default() -> Self {
			Self
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig {
		fn build(&self) {
			StorageVersion::<T>::put(Releases::V2);
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_finalize(_: T::BlockNumber) {
			<NextFeeMultiplier<T>>::mutate(|fm| {
				*fm = T::FeeMultiplierUpdate::convert(*fm);
			});
		}

		fn integrity_test() {
			// given weight == u64, we build multipliers from `diff` of two weight values, which can
			// at most be maximum block weight. Make sure that this can fit in a multiplier without
			// loss.
			use sp_std::convert::TryInto;
			assert!(
				<Multiplier as sp_runtime::traits::Bounded>::max_value() >=
					Multiplier::checked_from_integer(
						T::BlockWeights::get().max_block.try_into().unwrap()
					)
					.unwrap(),
			);

			let target = T::FeeMultiplierUpdate::target() *
				T::BlockWeights::get().get(DispatchClass::Normal).max_total.expect(
					"Setting `max_total` for `Normal` dispatch class is not compatible with \
					`transaction-payment` pallet.",
				);
			// add 1 percent;
			let addition = target / 100;
			if addition == 0 {
				// this is most likely because in a test setup we set everything to ().
				return
			}

			#[cfg(any(feature = "std", test))]
			sp_io::TestExternalities::new_empty().execute_with(|| {
				// This is the minimum value of the multiplier. Make sure that if we collapse to
				// this value, we can recover with a reasonable amount of traffic. For this test we
				// assert that if we collapse to minimum, the trend will be positive with a weight
				// value which is 1% more than the target.
				let min_value = T::FeeMultiplierUpdate::min();

				let target = target + addition;

				<frame_system::Pallet<T>>::set_block_consumed_resources(target, 0);
				let next = T::FeeMultiplierUpdate::convert(min_value);
				assert!(
					next > min_value,
					"The minimum bound of the multiplier is too low. When \
					block saturation is more than target by 1% and multiplier is minimal then \
					the multiplier doesn't increase."
				);
			});
		}
	}
}

impl<T: Config> Pallet<T>
where
	BalanceOf<T>: FixedPointOperand,
{
	/// Query the data that we know about the fee of a given `call`.
	///
	/// This pallet is not and cannot be aware of the internals of a signed extension, for example
	/// a tip. It only interprets the extrinsic as some encoded value and accounts for its weight
	/// and length, the runtime's extrinsic base weight, and the current fee multiplier.
	///
	/// All dispatchables must be annotated with weight and will have some fee info. This function
	/// always returns.
	pub fn query_info<Extrinsic: sp_runtime::traits::Extrinsic + GetDispatchInfo>(
		unchecked_extrinsic: Extrinsic,
		len: u32,
	) -> RuntimeDispatchInfo<BalanceOf<T>>
	where
		T::Call: Dispatchable<Info = DispatchInfo>,
	{
		// NOTE: we can actually make it understand `ChargeTransactionPayment`, but would be some
		// hassle for sure. We have to make it aware of the index of `ChargeTransactionPayment` in
		// `Extra`. Alternatively, we could actually execute the tx's per-dispatch and record the
		// balance of the sender before and after the pipeline.. but this is way too much hassle for
		// a very very little potential gain in the future.
		let dispatch_info = <Extrinsic as GetDispatchInfo>::get_dispatch_info(&unchecked_extrinsic);

		let partial_fee = if unchecked_extrinsic.is_signed().unwrap_or(false) {
			Self::compute_fee(len, &dispatch_info, 0u32.into())
		} else {
			// Unsigned extrinsics have no partial fee.
			0u32.into()
		};

		let DispatchInfo { weight, class, .. } = dispatch_info;

		RuntimeDispatchInfo { weight, class, partial_fee }
	}

	/// Query the detailed fee of a given `call`.
	pub fn query_fee_details<Extrinsic: sp_runtime::traits::Extrinsic + GetDispatchInfo>(
		unchecked_extrinsic: Extrinsic,
		len: u32,
	) -> FeeDetails<BalanceOf<T>>
	where
		T::Call: Dispatchable<Info = DispatchInfo>,
	{
		let dispatch_info = <Extrinsic as GetDispatchInfo>::get_dispatch_info(&unchecked_extrinsic);

		let tip = 0u32.into();

		if unchecked_extrinsic.is_signed().unwrap_or(false) {
			Self::compute_fee_details(len, &dispatch_info, tip)
		} else {
			// Unsigned extrinsics have no inclusion fee.
			FeeDetails { inclusion_fee: None, tip }
		}
	}

	/// Compute the final fee value for a particular transaction.
	pub fn compute_fee(len: u32, info: &DispatchInfoOf<T::Call>, tip: BalanceOf<T>) -> BalanceOf<T>
	where
		T::Call: Dispatchable<Info = DispatchInfo>,
	{
		Self::compute_fee_details(len, info, tip).final_fee()
	}

	/// Compute the fee details for a particular transaction.
	pub fn compute_fee_details(
		len: u32,
		info: &DispatchInfoOf<T::Call>,
		tip: BalanceOf<T>,
	) -> FeeDetails<BalanceOf<T>>
	where
		T::Call: Dispatchable<Info = DispatchInfo>,
	{
		Self::compute_fee_raw(len, info.weight, tip, info.pays_fee, info.class)
	}

	/// Compute the actual post dispatch fee for a particular transaction.
	///
	/// Identical to `compute_fee` with the only difference that the post dispatch corrected
	/// weight is used for the weight fee calculation.
	pub fn compute_actual_fee(
		len: u32,
		info: &DispatchInfoOf<T::Call>,
		post_info: &PostDispatchInfoOf<T::Call>,
		tip: BalanceOf<T>,
	) -> BalanceOf<T>
	where
		T::Call: Dispatchable<Info = DispatchInfo, PostInfo = PostDispatchInfo>,
	{
		Self::compute_actual_fee_details(len, info, post_info, tip).final_fee()
	}

	/// Compute the actual post dispatch fee details for a particular transaction.
	pub fn compute_actual_fee_details(
		len: u32,
		info: &DispatchInfoOf<T::Call>,
		post_info: &PostDispatchInfoOf<T::Call>,
		tip: BalanceOf<T>,
	) -> FeeDetails<BalanceOf<T>>
	where
		T::Call: Dispatchable<Info = DispatchInfo, PostInfo = PostDispatchInfo>,
	{
		Self::compute_fee_raw(
			len,
			post_info.calc_actual_weight(info),
			tip,
			post_info.pays_fee(info),
			info.class,
		)
	}

	fn compute_fee_raw(
		len: u32,
		weight: Weight,
		tip: BalanceOf<T>,
		pays_fee: Pays,
		class: DispatchClass,
	) -> FeeDetails<BalanceOf<T>> {
		if pays_fee == Pays::Yes {
			let len = <BalanceOf<T>>::from(len);
			let per_byte = T::TransactionByteFee::get();

			// length fee. this is not adjusted.
			let fixed_len_fee = per_byte.saturating_mul(len);

			// the adjustable part of the fee.
			let unadjusted_weight_fee = Self::weight_to_fee(weight);
			let multiplier = Self::next_fee_multiplier();
			// final adjusted weight fee.
			let adjusted_weight_fee = multiplier.saturating_mul_int(unadjusted_weight_fee);

			let base_fee = Self::weight_to_fee(T::BlockWeights::get().get(class).base_extrinsic);
			FeeDetails {
				inclusion_fee: Some(InclusionFee {
					base_fee,
					len_fee: fixed_len_fee,
					adjusted_weight_fee,
				}),
				tip,
			}
		} else {
			FeeDetails { inclusion_fee: None, tip }
		}
	}

	fn weight_to_fee(weight: Weight) -> BalanceOf<T> {
		// cap the weight to the maximum defined in runtime, otherwise it will be the
		// `Bounded` maximum of its data type, which is not desired.
		let capped_weight = weight.min(T::BlockWeights::get().max_block);
		T::WeightToFee::calc(&capped_weight)
	}
}

impl<T> Convert<Weight, BalanceOf<T>> for Pallet<T>
where
	T: Config,
	BalanceOf<T>: FixedPointOperand,
{
	/// Compute the fee for the specified weight.
	///
	/// This fee is already adjusted by the per block fee adjustment factor and is therefore the
	/// share that the weight contributes to the overall fee of a transaction. It is mainly
	/// for informational purposes and not used in the actual fee calculation.
	fn convert(weight: Weight) -> BalanceOf<T> {
		<NextFeeMultiplier<T>>::get().saturating_mul_int(Self::weight_to_fee(weight))
	}
}

/// Require the transactor pay for themselves and maybe include a tip to gain additional priority
/// in the queue.
///
/// # Transaction Validity
///
/// This extension sets the `priority` field of `TransactionValidity` depending on the amount
/// of tip being paid per weight unit.
///
/// Operational transactions will receive an additional priority bump, so that they are normally
/// considered before regular transactions.
#[derive(Encode, Decode, Clone, Eq, PartialEq, TypeInfo)]
#[scale_info(skip_type_params(T))]
pub struct ChargeTransactionPayment<T: Config>(#[codec(compact)] BalanceOf<T>);

impl<T: Config> ChargeTransactionPayment<T>
where
	T::Call: Dispatchable<Info = DispatchInfo, PostInfo = PostDispatchInfo>,
	BalanceOf<T>: Send + Sync + FixedPointOperand,
{
	/// utility constructor. Used only in client/factory code.
	pub fn from(fee: BalanceOf<T>) -> Self {
		Self(fee)
	}

	/// Returns the tip as being choosen by the transaction sender.
	pub fn tip(&self) -> BalanceOf<T> {
		self.0
	}

	fn withdraw_fee(
		&self,
		who: &T::AccountId,
		call: &T::Call,
		info: &DispatchInfoOf<T::Call>,
		len: usize,
	) -> Result<
		(
			BalanceOf<T>,
			<<T as Config>::OnChargeTransaction as OnChargeTransaction<T>>::LiquidityInfo,
		),
		TransactionValidityError,
	> {
		let tip = self.0;
		let fee = Pallet::<T>::compute_fee(len as u32, info, tip);

		<<T as Config>::OnChargeTransaction as OnChargeTransaction<T>>::withdraw_fee(
			who, call, info, fee, tip,
		)
		.map(|i| (fee, i))
	}

	/// Get an appropriate priority for a transaction with the given `DispatchInfo`, encoded length
	/// and user-included tip.
	///
	/// The priority is based on the amount of `tip` the user is willing to pay per unit of either
	/// `weight` or `length`, depending which one is more limitting. For `Operational` extrinsics
	/// we add a "virtual tip" to the calculations.
	///
	/// The formula should simply be `tip / bounded_{weight|length}`, but since we are using
	/// integer division, we have no guarantees it's going to give results in any reasonable
	/// range (might simply end up being zero). Hence we use a scaling factor:
	/// `tip * (max_block_{weight|length} / bounded_{weight|length})`, since given current
	/// state of-the-art blockchains, number of per-block transactions is expected to be in a
	/// range reasonable enough to not saturate the `Balance` type while multiplying by the tip.
	pub fn get_priority(
		info: &DispatchInfoOf<T::Call>,
		len: usize,
		tip: BalanceOf<T>,
		final_fee: BalanceOf<T>,
	) -> TransactionPriority {
		// Calculate how many such extrinsics we could fit into an empty block and take
		// the limitting factor.
		let max_block_weight = T::BlockWeights::get().max_block;
		let max_block_length = *T::BlockLength::get().max.get(info.class) as u64;

		let bounded_weight = info.weight.max(1).min(max_block_weight);
		let bounded_length = (len as u64).max(1).min(max_block_length);

		let max_tx_per_block_weight = max_block_weight / bounded_weight;
		let max_tx_per_block_length = max_block_length / bounded_length;
		// Given our current knowledge this value is going to be in a reasonable range - i.e.
		// less than 10^9 (2^30), so multiplying by the `tip` value is unlikely to overflow the
		// balance type. We still use saturating ops obviously, but the point is to end up with some
		// `priority` distribution instead of having all transactions saturate the priority.
		let max_tx_per_block = max_tx_per_block_length
			.min(max_tx_per_block_weight)
			.saturated_into::<BalanceOf<T>>();
		let max_reward = |val: BalanceOf<T>| val.saturating_mul(max_tx_per_block);

		// To distribute no-tip transactions a little bit, we set the minimal tip as `1`.
		// This means that given two transactions without a tip, smaller one will be preferred.
		let tip = tip.max(1.saturated_into());
		let scaled_tip = max_reward(tip);

		match info.class {
			DispatchClass::Normal => {
				// For normal class we simply take the `tip_per_weight`.
				scaled_tip
			},
			DispatchClass::Mandatory => {
				// Mandatory extrinsics should be prohibited (e.g. by the [`CheckWeight`]
				// extensions), but just to be safe let's return the same priority as `Normal` here.
				scaled_tip
			},
			DispatchClass::Operational => {
				// A "virtual tip" value added to an `Operational` extrinsic.
				// This value should be kept high enough to allow `Operational` extrinsics
				// to get in even during congestion period, but at the same time low
				// enough to prevent a possible spam attack by sending invalid operational
				// extrinsics which push away regular transactions from the pool.
				let fee_multiplier = T::OperationalFeeMultiplier::get().saturated_into();
				let virtual_tip = final_fee.saturating_mul(fee_multiplier);
				let scaled_virtual_tip = max_reward(virtual_tip);

				scaled_tip.saturating_add(scaled_virtual_tip)
			},
		}
		.saturated_into::<TransactionPriority>()
	}
}

impl<T: Config> sp_std::fmt::Debug for ChargeTransactionPayment<T> {
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		write!(f, "ChargeTransactionPayment<{:?}>", self.0)
	}
	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		Ok(())
	}
}

impl<T: Config> SignedExtension for ChargeTransactionPayment<T>
where
	BalanceOf<T>: Send + Sync + From<u64> + FixedPointOperand,
	T::Call: Dispatchable<Info = DispatchInfo, PostInfo = PostDispatchInfo>,
{
	const IDENTIFIER: &'static str = "ChargeTransactionPayment";
	type AccountId = T::AccountId;
	type Call = T::Call;
	type AdditionalSigned = ();
	type Pre = (
		// tip
		BalanceOf<T>,
		// who paid the fee
		Self::AccountId,
		// imbalance resulting from withdrawing the fee
		<<T as Config>::OnChargeTransaction as OnChargeTransaction<T>>::LiquidityInfo,
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
		let (final_fee, _) = self.withdraw_fee(who, call, info, len)?;
		let tip = self.0;
		Ok(ValidTransaction {
			priority: Self::get_priority(info, len, tip, final_fee),
			..Default::default()
		})
	}

	fn pre_dispatch(
		self,
		who: &Self::AccountId,
		call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> Result<Self::Pre, TransactionValidityError> {
		let (_fee, imbalance) = self.withdraw_fee(who, call, info, len)?;
		Ok((self.0, who.clone(), imbalance))
	}

	fn post_dispatch(
		pre: Self::Pre,
		info: &DispatchInfoOf<Self::Call>,
		post_info: &PostDispatchInfoOf<Self::Call>,
		len: usize,
		_result: &DispatchResult,
	) -> Result<(), TransactionValidityError> {
		let (tip, who, imbalance) = pre;
		let actual_fee = Pallet::<T>::compute_actual_fee(len as u32, info, post_info, tip);
		T::OnChargeTransaction::correct_and_deposit_fee(
			&who, info, post_info, actual_fee, tip, imbalance,
		)?;
		Ok(())
	}
}

impl<T: Config, AnyCall: GetDispatchInfo + Encode> EstimateCallFee<AnyCall, BalanceOf<T>>
	for Pallet<T>
where
	BalanceOf<T>: FixedPointOperand,
	T::Call: Dispatchable<Info = DispatchInfo, PostInfo = PostDispatchInfo>,
{
	fn estimate_call_fee(call: &AnyCall, post_info: PostDispatchInfo) -> BalanceOf<T> {
		let len = call.encoded_size() as u32;
		let info = call.get_dispatch_info();
		Self::compute_actual_fee(len, &info, &post_info, Zero::zero())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate as pallet_transaction_payment;

	use std::cell::RefCell;

	use codec::Encode;
	use smallvec::smallvec;

	use sp_core::H256;
	use sp_runtime::{
		testing::{Header, TestXt},
		traits::{BlakeTwo256, IdentityLookup, One},
		transaction_validity::InvalidTransaction,
		Perbill,
	};

	use frame_support::{
		assert_noop, assert_ok, parameter_types,
		traits::{Currency, Imbalance, OnUnbalanced},
		weights::{
			DispatchClass, DispatchInfo, GetDispatchInfo, PostDispatchInfo, Weight,
			WeightToFeeCoefficient, WeightToFeeCoefficients, WeightToFeePolynomial,
		},
	};
	use frame_system as system;
	use pallet_balances::Call as BalancesCall;

	type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Runtime>;
	type Block = frame_system::mocking::MockBlock<Runtime>;

	frame_support::construct_runtime!(
		pub enum Runtime where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic,
		{
			System: system::{Pallet, Call, Config, Storage, Event<T>},
			Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
			TransactionPayment: pallet_transaction_payment::{Pallet, Storage},
		}
	);

	const CALL: &<Runtime as frame_system::Config>::Call =
		&Call::Balances(BalancesCall::transfer { dest: 2, value: 69 });

	thread_local! {
		static EXTRINSIC_BASE_WEIGHT: RefCell<u64> = RefCell::new(0);
	}

	pub struct BlockWeights;
	impl Get<frame_system::limits::BlockWeights> for BlockWeights {
		fn get() -> frame_system::limits::BlockWeights {
			frame_system::limits::BlockWeights::builder()
				.base_block(0)
				.for_class(DispatchClass::all(), |weights| {
					weights.base_extrinsic = EXTRINSIC_BASE_WEIGHT.with(|v| *v.borrow()).into();
				})
				.for_class(DispatchClass::non_mandatory(), |weights| {
					weights.max_total = 1024.into();
				})
				.build_or_panic()
		}
	}

	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub static TransactionByteFee: u64 = 1;
		pub static WeightToFee: u64 = 1;
		pub static OperationalFeeMultiplier: u8 = 5;
	}

	impl frame_system::Config for Runtime {
		type BaseCallFilter = frame_support::traits::Everything;
		type BlockWeights = BlockWeights;
		type BlockLength = ();
		type DbWeight = ();
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Call = Call;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = Event;
		type BlockHashCount = BlockHashCount;
		type Version = ();
		type PalletInfo = PalletInfo;
		type AccountData = pallet_balances::AccountData<u64>;
		type OnNewAccount = ();
		type OnKilledAccount = ();
		type SystemWeightInfo = ();
		type SS58Prefix = ();
		type OnSetCode = ();
	}

	parameter_types! {
		pub const ExistentialDeposit: u64 = 1;
	}

	impl pallet_balances::Config for Runtime {
		type Balance = u64;
		type Event = Event;
		type DustRemoval = ();
		type ExistentialDeposit = ExistentialDeposit;
		type AccountStore = System;
		type MaxLocks = ();
		type MaxReserves = ();
		type ReserveIdentifier = [u8; 8];
		type WeightInfo = ();
	}

	impl WeightToFeePolynomial for WeightToFee {
		type Balance = u64;

		fn polynomial() -> WeightToFeeCoefficients<Self::Balance> {
			smallvec![WeightToFeeCoefficient {
				degree: 1,
				coeff_frac: Perbill::zero(),
				coeff_integer: WEIGHT_TO_FEE.with(|v| *v.borrow()),
				negative: false,
			}]
		}
	}

	thread_local! {
		static TIP_UNBALANCED_AMOUNT: RefCell<u64> = RefCell::new(0);
		static FEE_UNBALANCED_AMOUNT: RefCell<u64> = RefCell::new(0);
	}

	pub struct DealWithFees;
	impl OnUnbalanced<pallet_balances::NegativeImbalance<Runtime>> for DealWithFees {
		fn on_unbalanceds<B>(
			mut fees_then_tips: impl Iterator<Item = pallet_balances::NegativeImbalance<Runtime>>,
		) {
			if let Some(fees) = fees_then_tips.next() {
				FEE_UNBALANCED_AMOUNT.with(|a| *a.borrow_mut() += fees.peek());
				if let Some(tips) = fees_then_tips.next() {
					TIP_UNBALANCED_AMOUNT.with(|a| *a.borrow_mut() += tips.peek());
				}
			}
		}
	}

	impl Config for Runtime {
		type OnChargeTransaction = CurrencyAdapter<Balances, DealWithFees>;
		type TransactionByteFee = TransactionByteFee;
		type OperationalFeeMultiplier = OperationalFeeMultiplier;
		type WeightToFee = WeightToFee;
		type FeeMultiplierUpdate = ();
	}

	pub struct ExtBuilder {
		balance_factor: u64,
		base_weight: u64,
		byte_fee: u64,
		weight_to_fee: u64,
	}

	impl Default for ExtBuilder {
		fn default() -> Self {
			Self { balance_factor: 1, base_weight: 0, byte_fee: 1, weight_to_fee: 1 }
		}
	}

	impl ExtBuilder {
		pub fn base_weight(mut self, base_weight: u64) -> Self {
			self.base_weight = base_weight;
			self
		}
		pub fn byte_fee(mut self, byte_fee: u64) -> Self {
			self.byte_fee = byte_fee;
			self
		}
		pub fn weight_fee(mut self, weight_to_fee: u64) -> Self {
			self.weight_to_fee = weight_to_fee;
			self
		}
		pub fn balance_factor(mut self, factor: u64) -> Self {
			self.balance_factor = factor;
			self
		}
		fn set_constants(&self) {
			EXTRINSIC_BASE_WEIGHT.with(|v| *v.borrow_mut() = self.base_weight);
			TRANSACTION_BYTE_FEE.with(|v| *v.borrow_mut() = self.byte_fee);
			WEIGHT_TO_FEE.with(|v| *v.borrow_mut() = self.weight_to_fee);
		}
		pub fn build(self) -> sp_io::TestExternalities {
			self.set_constants();
			let mut t = frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();
			pallet_balances::GenesisConfig::<Runtime> {
				balances: if self.balance_factor > 0 {
					vec![
						(1, 10 * self.balance_factor),
						(2, 20 * self.balance_factor),
						(3, 30 * self.balance_factor),
						(4, 40 * self.balance_factor),
						(5, 50 * self.balance_factor),
						(6, 60 * self.balance_factor),
					]
				} else {
					vec![]
				},
			}
			.assimilate_storage(&mut t)
			.unwrap();
			t.into()
		}
	}

	/// create a transaction info struct from weight. Handy to avoid building the whole struct.
	pub fn info_from_weight(w: Weight) -> DispatchInfo {
		// pays_fee: Pays::Yes -- class: DispatchClass::Normal
		DispatchInfo { weight: w, ..Default::default() }
	}

	fn post_info_from_weight(w: Weight) -> PostDispatchInfo {
		PostDispatchInfo { actual_weight: Some(w), pays_fee: Default::default() }
	}

	fn post_info_from_pays(p: Pays) -> PostDispatchInfo {
		PostDispatchInfo { actual_weight: None, pays_fee: p }
	}

	fn default_post_info() -> PostDispatchInfo {
		PostDispatchInfo { actual_weight: None, pays_fee: Default::default() }
	}

	#[test]
	fn signed_extension_transaction_payment_work() {
		ExtBuilder::default()
			.balance_factor(10)
			.base_weight(5)
			.build()
			.execute_with(|| {
				let len = 10;
				let pre = ChargeTransactionPayment::<Runtime>::from(0)
					.pre_dispatch(&1, CALL, &info_from_weight(5), len)
					.unwrap();
				assert_eq!(Balances::free_balance(1), 100 - 5 - 5 - 10);

				assert_ok!(ChargeTransactionPayment::<Runtime>::post_dispatch(
					pre,
					&info_from_weight(5),
					&default_post_info(),
					len,
					&Ok(())
				));
				assert_eq!(Balances::free_balance(1), 100 - 5 - 5 - 10);
				assert_eq!(FEE_UNBALANCED_AMOUNT.with(|a| a.borrow().clone()), 5 + 5 + 10);
				assert_eq!(TIP_UNBALANCED_AMOUNT.with(|a| a.borrow().clone()), 0);

				FEE_UNBALANCED_AMOUNT.with(|a| *a.borrow_mut() = 0);

				let pre = ChargeTransactionPayment::<Runtime>::from(5 /* tipped */)
					.pre_dispatch(&2, CALL, &info_from_weight(100), len)
					.unwrap();
				assert_eq!(Balances::free_balance(2), 200 - 5 - 10 - 100 - 5);

				assert_ok!(ChargeTransactionPayment::<Runtime>::post_dispatch(
					pre,
					&info_from_weight(100),
					&post_info_from_weight(50),
					len,
					&Ok(())
				));
				assert_eq!(Balances::free_balance(2), 200 - 5 - 10 - 50 - 5);
				assert_eq!(FEE_UNBALANCED_AMOUNT.with(|a| a.borrow().clone()), 5 + 10 + 50);
				assert_eq!(TIP_UNBALANCED_AMOUNT.with(|a| a.borrow().clone()), 5);
			});
	}

	#[test]
	fn signed_extension_transaction_payment_multiplied_refund_works() {
		ExtBuilder::default()
			.balance_factor(10)
			.base_weight(5)
			.build()
			.execute_with(|| {
				let len = 10;
				<NextFeeMultiplier<Runtime>>::put(Multiplier::saturating_from_rational(3, 2));

				let pre = ChargeTransactionPayment::<Runtime>::from(5 /* tipped */)
					.pre_dispatch(&2, CALL, &info_from_weight(100), len)
					.unwrap();
				// 5 base fee, 10 byte fee, 3/2 * 100 weight fee, 5 tip
				assert_eq!(Balances::free_balance(2), 200 - 5 - 10 - 150 - 5);

				assert_ok!(ChargeTransactionPayment::<Runtime>::post_dispatch(
					pre,
					&info_from_weight(100),
					&post_info_from_weight(50),
					len,
					&Ok(())
				));
				// 75 (3/2 of the returned 50 units of weight) is refunded
				assert_eq!(Balances::free_balance(2), 200 - 5 - 10 - 75 - 5);
			});
	}

	#[test]
	fn signed_extension_transaction_payment_is_bounded() {
		ExtBuilder::default().balance_factor(1000).byte_fee(0).build().execute_with(|| {
			// maximum weight possible
			assert_ok!(ChargeTransactionPayment::<Runtime>::from(0).pre_dispatch(
				&1,
				CALL,
				&info_from_weight(Weight::max_value()),
				10
			));
			// fee will be proportional to what is the actual maximum weight in the runtime.
			assert_eq!(
				Balances::free_balance(&1),
				(10000 - <Runtime as frame_system::Config>::BlockWeights::get().max_block) as u64
			);
		});
	}

	#[test]
	fn signed_extension_allows_free_transactions() {
		ExtBuilder::default()
			.base_weight(100)
			.balance_factor(0)
			.build()
			.execute_with(|| {
				// 1 ain't have a penny.
				assert_eq!(Balances::free_balance(1), 0);

				let len = 100;

				// This is a completely free (and thus wholly insecure/DoS-ridden) transaction.
				let operational_transaction = DispatchInfo {
					weight: 0,
					class: DispatchClass::Operational,
					pays_fee: Pays::No,
				};
				assert_ok!(ChargeTransactionPayment::<Runtime>::from(0).validate(
					&1,
					CALL,
					&operational_transaction,
					len
				));

				// like a InsecureFreeNormal
				let free_transaction =
					DispatchInfo { weight: 0, class: DispatchClass::Normal, pays_fee: Pays::Yes };
				assert_noop!(
					ChargeTransactionPayment::<Runtime>::from(0).validate(
						&1,
						CALL,
						&free_transaction,
						len
					),
					TransactionValidityError::Invalid(InvalidTransaction::Payment),
				);
			});
	}

	#[test]
	fn signed_ext_length_fee_is_also_updated_per_congestion() {
		ExtBuilder::default()
			.base_weight(5)
			.balance_factor(10)
			.build()
			.execute_with(|| {
				// all fees should be x1.5
				<NextFeeMultiplier<Runtime>>::put(Multiplier::saturating_from_rational(3, 2));
				let len = 10;

				assert_ok!(ChargeTransactionPayment::<Runtime>::from(10) // tipped
					.pre_dispatch(&1, CALL, &info_from_weight(3), len));
				assert_eq!(
					Balances::free_balance(1),
					100 // original
				- 10 // tip
				- 5 // base
				- 10 // len
				- (3 * 3 / 2) // adjusted weight
				);
			})
	}

	#[test]
	fn query_info_and_fee_details_works() {
		let call = Call::Balances(BalancesCall::transfer { dest: 2, value: 69 });
		let origin = 111111;
		let extra = ();
		let xt = TestXt::new(call.clone(), Some((origin, extra)));
		let info = xt.get_dispatch_info();
		let ext = xt.encode();
		let len = ext.len() as u32;

		let unsigned_xt = TestXt::<_, ()>::new(call, None);
		let unsigned_xt_info = unsigned_xt.get_dispatch_info();

		ExtBuilder::default().base_weight(5).weight_fee(2).build().execute_with(|| {
			// all fees should be x1.5
			<NextFeeMultiplier<Runtime>>::put(Multiplier::saturating_from_rational(3, 2));

			assert_eq!(
				TransactionPayment::query_info(xt.clone(), len),
				RuntimeDispatchInfo {
					weight: info.weight,
					class: info.class,
					partial_fee: 5 * 2 /* base * weight_fee */
						+ len as u64  /* len * 1 */
						+ info.weight.min(BlockWeights::get().max_block) as u64 * 2 * 3 / 2 /* weight */
				},
			);

			assert_eq!(
				TransactionPayment::query_info(unsigned_xt.clone(), len),
				RuntimeDispatchInfo {
					weight: unsigned_xt_info.weight,
					class: unsigned_xt_info.class,
					partial_fee: 0,
				},
			);

			assert_eq!(
				TransactionPayment::query_fee_details(xt, len),
				FeeDetails {
					inclusion_fee: Some(InclusionFee {
						base_fee: 5 * 2,
						len_fee: len as u64,
						adjusted_weight_fee: info.weight.min(BlockWeights::get().max_block) as u64 *
							2 * 3 / 2
					}),
					tip: 0,
				},
			);

			assert_eq!(
				TransactionPayment::query_fee_details(unsigned_xt, len),
				FeeDetails { inclusion_fee: None, tip: 0 },
			);
		});
	}

	#[test]
	fn compute_fee_works_without_multiplier() {
		ExtBuilder::default()
			.base_weight(100)
			.byte_fee(10)
			.balance_factor(0)
			.build()
			.execute_with(|| {
				// Next fee multiplier is zero
				assert_eq!(<NextFeeMultiplier<Runtime>>::get(), Multiplier::one());

				// Tip only, no fees works
				let dispatch_info = DispatchInfo {
					weight: 0,
					class: DispatchClass::Operational,
					pays_fee: Pays::No,
				};
				assert_eq!(Pallet::<Runtime>::compute_fee(0, &dispatch_info, 10), 10);
				// No tip, only base fee works
				let dispatch_info = DispatchInfo {
					weight: 0,
					class: DispatchClass::Operational,
					pays_fee: Pays::Yes,
				};
				assert_eq!(Pallet::<Runtime>::compute_fee(0, &dispatch_info, 0), 100);
				// Tip + base fee works
				assert_eq!(Pallet::<Runtime>::compute_fee(0, &dispatch_info, 69), 169);
				// Len (byte fee) + base fee works
				assert_eq!(Pallet::<Runtime>::compute_fee(42, &dispatch_info, 0), 520);
				// Weight fee + base fee works
				let dispatch_info = DispatchInfo {
					weight: 1000,
					class: DispatchClass::Operational,
					pays_fee: Pays::Yes,
				};
				assert_eq!(Pallet::<Runtime>::compute_fee(0, &dispatch_info, 0), 1100);
			});
	}

	#[test]
	fn compute_fee_works_with_multiplier() {
		ExtBuilder::default()
			.base_weight(100)
			.byte_fee(10)
			.balance_factor(0)
			.build()
			.execute_with(|| {
				// Add a next fee multiplier. Fees will be x3/2.
				<NextFeeMultiplier<Runtime>>::put(Multiplier::saturating_from_rational(3, 2));
				// Base fee is unaffected by multiplier
				let dispatch_info = DispatchInfo {
					weight: 0,
					class: DispatchClass::Operational,
					pays_fee: Pays::Yes,
				};
				assert_eq!(Pallet::<Runtime>::compute_fee(0, &dispatch_info, 0), 100);

				// Everything works together :)
				let dispatch_info = DispatchInfo {
					weight: 123,
					class: DispatchClass::Operational,
					pays_fee: Pays::Yes,
				};
				// 123 weight, 456 length, 100 base
				assert_eq!(
					Pallet::<Runtime>::compute_fee(456, &dispatch_info, 789),
					100 + (3 * 123 / 2) + 4560 + 789,
				);
			});
	}

	#[test]
	fn compute_fee_works_with_negative_multiplier() {
		ExtBuilder::default()
			.base_weight(100)
			.byte_fee(10)
			.balance_factor(0)
			.build()
			.execute_with(|| {
				// Add a next fee multiplier. All fees will be x1/2.
				<NextFeeMultiplier<Runtime>>::put(Multiplier::saturating_from_rational(1, 2));

				// Base fee is unaffected by multiplier.
				let dispatch_info = DispatchInfo {
					weight: 0,
					class: DispatchClass::Operational,
					pays_fee: Pays::Yes,
				};
				assert_eq!(Pallet::<Runtime>::compute_fee(0, &dispatch_info, 0), 100);

				// Everything works together.
				let dispatch_info = DispatchInfo {
					weight: 123,
					class: DispatchClass::Operational,
					pays_fee: Pays::Yes,
				};
				// 123 weight, 456 length, 100 base
				assert_eq!(
					Pallet::<Runtime>::compute_fee(456, &dispatch_info, 789),
					100 + (123 / 2) + 4560 + 789,
				);
			});
	}

	#[test]
	fn compute_fee_does_not_overflow() {
		ExtBuilder::default()
			.base_weight(100)
			.byte_fee(10)
			.balance_factor(0)
			.build()
			.execute_with(|| {
				// Overflow is handled
				let dispatch_info = DispatchInfo {
					weight: Weight::max_value(),
					class: DispatchClass::Operational,
					pays_fee: Pays::Yes,
				};
				assert_eq!(
					Pallet::<Runtime>::compute_fee(u32::MAX, &dispatch_info, u64::MAX),
					u64::MAX
				);
			});
	}

	#[test]
	fn refund_does_not_recreate_account() {
		ExtBuilder::default()
			.balance_factor(10)
			.base_weight(5)
			.build()
			.execute_with(|| {
				// So events are emitted
				System::set_block_number(10);
				let len = 10;
				let pre = ChargeTransactionPayment::<Runtime>::from(5 /* tipped */)
					.pre_dispatch(&2, CALL, &info_from_weight(100), len)
					.unwrap();
				assert_eq!(Balances::free_balance(2), 200 - 5 - 10 - 100 - 5);

				// kill the account between pre and post dispatch
				assert_ok!(Balances::transfer(Some(2).into(), 3, Balances::free_balance(2)));
				assert_eq!(Balances::free_balance(2), 0);

				assert_ok!(ChargeTransactionPayment::<Runtime>::post_dispatch(
					pre,
					&info_from_weight(100),
					&post_info_from_weight(50),
					len,
					&Ok(())
				));
				assert_eq!(Balances::free_balance(2), 0);
				// Transfer Event
				System::assert_has_event(Event::Balances(pallet_balances::Event::Transfer(
					2, 3, 80,
				)));
				// Killed Event
				System::assert_has_event(Event::System(system::Event::KilledAccount(2)));
			});
	}

	#[test]
	fn actual_weight_higher_than_max_refunds_nothing() {
		ExtBuilder::default()
			.balance_factor(10)
			.base_weight(5)
			.build()
			.execute_with(|| {
				let len = 10;
				let pre = ChargeTransactionPayment::<Runtime>::from(5 /* tipped */)
					.pre_dispatch(&2, CALL, &info_from_weight(100), len)
					.unwrap();
				assert_eq!(Balances::free_balance(2), 200 - 5 - 10 - 100 - 5);

				assert_ok!(ChargeTransactionPayment::<Runtime>::post_dispatch(
					pre,
					&info_from_weight(100),
					&post_info_from_weight(101),
					len,
					&Ok(())
				));
				assert_eq!(Balances::free_balance(2), 200 - 5 - 10 - 100 - 5);
			});
	}

	#[test]
	fn zero_transfer_on_free_transaction() {
		ExtBuilder::default()
			.balance_factor(10)
			.base_weight(5)
			.build()
			.execute_with(|| {
				// So events are emitted
				System::set_block_number(10);
				let len = 10;
				let dispatch_info =
					DispatchInfo { weight: 100, pays_fee: Pays::No, class: DispatchClass::Normal };
				let user = 69;
				let pre = ChargeTransactionPayment::<Runtime>::from(0)
					.pre_dispatch(&user, CALL, &dispatch_info, len)
					.unwrap();
				assert_eq!(Balances::total_balance(&user), 0);
				assert_ok!(ChargeTransactionPayment::<Runtime>::post_dispatch(
					pre,
					&dispatch_info,
					&default_post_info(),
					len,
					&Ok(())
				));
				assert_eq!(Balances::total_balance(&user), 0);
				// No events for such a scenario
				assert_eq!(System::events().len(), 0);
			});
	}

	#[test]
	fn refund_consistent_with_actual_weight() {
		ExtBuilder::default()
			.balance_factor(10)
			.base_weight(7)
			.build()
			.execute_with(|| {
				let info = info_from_weight(100);
				let post_info = post_info_from_weight(33);
				let prev_balance = Balances::free_balance(2);
				let len = 10;
				let tip = 5;

				<NextFeeMultiplier<Runtime>>::put(Multiplier::saturating_from_rational(5, 4));

				let pre = ChargeTransactionPayment::<Runtime>::from(tip)
					.pre_dispatch(&2, CALL, &info, len)
					.unwrap();

				ChargeTransactionPayment::<Runtime>::post_dispatch(
					pre,
					&info,
					&post_info,
					len,
					&Ok(()),
				)
				.unwrap();

				let refund_based_fee = prev_balance - Balances::free_balance(2);
				let actual_fee =
					Pallet::<Runtime>::compute_actual_fee(len as u32, &info, &post_info, tip);

				// 33 weight, 10 length, 7 base, 5 tip
				assert_eq!(actual_fee, 7 + 10 + (33 * 5 / 4) + 5);
				assert_eq!(refund_based_fee, actual_fee);
			});
	}

	#[test]
	fn should_alter_operational_priority() {
		let tip = 5;
		let len = 10;

		ExtBuilder::default().balance_factor(100).build().execute_with(|| {
			let normal =
				DispatchInfo { weight: 100, class: DispatchClass::Normal, pays_fee: Pays::Yes };
			let priority = ChargeTransactionPayment::<Runtime>(tip)
				.validate(&2, CALL, &normal, len)
				.unwrap()
				.priority;

			assert_eq!(priority, 50);

			let priority = ChargeTransactionPayment::<Runtime>(2 * tip)
				.validate(&2, CALL, &normal, len)
				.unwrap()
				.priority;

			assert_eq!(priority, 100);
		});

		ExtBuilder::default().balance_factor(100).build().execute_with(|| {
			let op = DispatchInfo {
				weight: 100,
				class: DispatchClass::Operational,
				pays_fee: Pays::Yes,
			};
			let priority = ChargeTransactionPayment::<Runtime>(tip)
				.validate(&2, CALL, &op, len)
				.unwrap()
				.priority;
			assert_eq!(priority, 5800);

			let priority = ChargeTransactionPayment::<Runtime>(2 * tip)
				.validate(&2, CALL, &op, len)
				.unwrap()
				.priority;
			assert_eq!(priority, 6100);
		});
	}

	#[test]
	fn no_tip_has_some_priority() {
		let tip = 0;
		let len = 10;

		ExtBuilder::default().balance_factor(100).build().execute_with(|| {
			let normal =
				DispatchInfo { weight: 100, class: DispatchClass::Normal, pays_fee: Pays::Yes };
			let priority = ChargeTransactionPayment::<Runtime>(tip)
				.validate(&2, CALL, &normal, len)
				.unwrap()
				.priority;

			assert_eq!(priority, 10);
		});

		ExtBuilder::default().balance_factor(100).build().execute_with(|| {
			let op = DispatchInfo {
				weight: 100,
				class: DispatchClass::Operational,
				pays_fee: Pays::Yes,
			};
			let priority = ChargeTransactionPayment::<Runtime>(tip)
				.validate(&2, CALL, &op, len)
				.unwrap()
				.priority;
			assert_eq!(priority, 5510);
		});
	}

	#[test]
	fn post_info_can_change_pays_fee() {
		ExtBuilder::default()
			.balance_factor(10)
			.base_weight(7)
			.build()
			.execute_with(|| {
				let info = info_from_weight(100);
				let post_info = post_info_from_pays(Pays::No);
				let prev_balance = Balances::free_balance(2);
				let len = 10;
				let tip = 5;

				<NextFeeMultiplier<Runtime>>::put(Multiplier::saturating_from_rational(5, 4));

				let pre = ChargeTransactionPayment::<Runtime>::from(tip)
					.pre_dispatch(&2, CALL, &info, len)
					.unwrap();

				ChargeTransactionPayment::<Runtime>::post_dispatch(
					pre,
					&info,
					&post_info,
					len,
					&Ok(()),
				)
				.unwrap();

				let refund_based_fee = prev_balance - Balances::free_balance(2);
				let actual_fee =
					Pallet::<Runtime>::compute_actual_fee(len as u32, &info, &post_info, tip);

				// Only 5 tip is paid
				assert_eq!(actual_fee, 5);
				assert_eq!(refund_based_fee, actual_fee);
			});
	}
}
