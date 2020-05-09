// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! # Transaction Payment Module
//!
//! This module provides the basic logic needed to pay the absolute minimum amount needed for a
//! transaction to be included. This includes:
//!   - _weight fee_: A fee proportional to amount of weight a transaction consumes.
//!   - _length fee_: A fee proportional to the encoded length of the transaction.
//!   - _tip_: An optional tip. Tip increases the priority of the transaction, giving it a higher
//!     chance to be included by the transaction queue.
//!
//! Additionally, this module allows one to configure:
//!   - The mapping between one unit of weight to one unit of fee via [`Trait::WeightToFee`].
//!   - A means of updating the fee for the next block, via defining a multiplier, based on the
//!     final state of the chain at the end of the previous block. This can be configured via
//!     [`Trait::FeeMultiplierUpdate`]

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;
use codec::{Encode, Decode};
use frame_support::{
	decl_storage, decl_module,
	traits::{Currency, Get, OnUnbalanced, ExistenceRequirement, WithdrawReason, Imbalance},
	weights::{Weight, DispatchInfo, PostDispatchInfo, GetDispatchInfo, Pays},
	dispatch::DispatchResult,
};
use sp_runtime::{
	Fixed128,
	transaction_validity::{
		TransactionPriority, ValidTransaction, InvalidTransaction, TransactionValidityError,
		TransactionValidity,
	},
	traits::{
		Zero, Saturating, SignedExtension, SaturatedConversion, Convert, Dispatchable,
		DispatchInfoOf, PostDispatchInfoOf, UniqueSaturatedFrom, UniqueSaturatedInto,
	},
};
use pallet_transaction_payment_rpc_runtime_api::RuntimeDispatchInfo;

type Multiplier = Fixed128;
type BalanceOf<T> =
	<<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;
type NegativeImbalanceOf<T> =
	<<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::NegativeImbalance;

pub trait Trait: frame_system::Trait {
	/// The currency type in which fees will be paid.
	type Currency: Currency<Self::AccountId> + Send + Sync;

	/// Handler for the unbalanced reduction when taking transaction fees. This is either one or
	/// two separate imbalances, the first is the transaction fee paid, the second is the tip paid,
	/// if any.
	type OnTransactionPayment: OnUnbalanced<NegativeImbalanceOf<Self>>;

	/// The fee to be paid for making a transaction; the per-byte portion.
	type TransactionByteFee: Get<BalanceOf<Self>>;

	/// Convert a weight value into a deductible fee based on the currency type.
	type WeightToFee: Convert<Weight, BalanceOf<Self>>;

	/// Update the multiplier of the next block, based on the previous block's weight.
	type FeeMultiplierUpdate: Convert<Multiplier, Multiplier>;
}

decl_storage! {
	trait Store for Module<T: Trait> as TransactionPayment {
		pub NextFeeMultiplier get(fn next_fee_multiplier): Multiplier = Multiplier::from_parts(0);
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		/// The fee to be paid for making a transaction; the per-byte portion.
		const TransactionByteFee: BalanceOf<T> = T::TransactionByteFee::get();

		fn on_finalize() {
			NextFeeMultiplier::mutate(|fm| {
				*fm = T::FeeMultiplierUpdate::convert(*fm)
			});
		}
	}
}

impl<T: Trait> Module<T> {
	/// Query the data that we know about the fee of a given `call`.
	///
	/// As this module is not and cannot be aware of the internals of a signed extension, it only
	/// interprets them as some encoded value and takes their length into account.
	///
	/// All dispatchables must be annotated with weight and will have some fee info. This function
	/// always returns.
	pub fn query_info<Extrinsic: GetDispatchInfo>(
		unchecked_extrinsic: Extrinsic,
		len: u32,
	) -> RuntimeDispatchInfo<BalanceOf<T>>
	where
		T: Send + Sync,
		BalanceOf<T>: Send + Sync,
		T::Call: Dispatchable<Info=DispatchInfo>,
	{
		// NOTE: we can actually make it understand `ChargeTransactionPayment`, but would be some
		// hassle for sure. We have to make it aware of the index of `ChargeTransactionPayment` in
		// `Extra`. Alternatively, we could actually execute the tx's per-dispatch and record the
		// balance of the sender before and after the pipeline.. but this is way too much hassle for
		// a very very little potential gain in the future.
		let dispatch_info = <Extrinsic as GetDispatchInfo>::get_dispatch_info(&unchecked_extrinsic);

		let partial_fee = Self::compute_fee(len, &dispatch_info, 0u32.into());
		let DispatchInfo { weight, class, .. } = dispatch_info;

		RuntimeDispatchInfo { weight, class, partial_fee }
	}

	/// Compute the final fee value for a particular transaction.
	///
	/// The final fee is composed of:
	///   - _base_fee_: This is the minimum amount a user pays for a transaction.
	///   - _len_fee_: This is the amount paid merely to pay for size of the transaction.
	///   - _weight_fee_: This amount is computed based on the weight of the transaction. Unlike
	///      size-fee, this is not input dependent and reflects the _complexity_ of the execution
	///      and the time it consumes.
	///   - _targeted_fee_adjustment_: This is a multiplier that can tune the final fee based on
	///     the congestion of the network.
	///   - (optional) _tip_: if included in the transaction, it will be added on top. Only signed
	///      transactions can have a tip.
	///
	/// final_fee = base_fee + targeted_fee_adjustment(len_fee + weight_fee) + tip;
	pub fn compute_fee(
		len: u32,
		info: &DispatchInfoOf<T::Call>,
		tip: BalanceOf<T>,
	) -> BalanceOf<T> where
		T::Call: Dispatchable<Info=DispatchInfo>,
	{
		if info.pays_fee == Pays::Yes {
			let len = <BalanceOf<T>>::from(len);
			let per_byte = T::TransactionByteFee::get();
			let len_fee = per_byte.saturating_mul(len);
			let unadjusted_weight_fee = Self::weight_to_fee(info.weight);

			// the adjustable part of the fee
			let adjustable_fee = len_fee.saturating_add(unadjusted_weight_fee);
			let targeted_fee_adjustment = NextFeeMultiplier::get();
			let adjusted_fee = targeted_fee_adjustment.saturated_multiply_accumulate(adjustable_fee.saturated_into());

			let base_fee = Self::weight_to_fee(T::ExtrinsicBaseWeight::get());
			base_fee.saturating_add(adjusted_fee.saturated_into()).saturating_add(tip)
		} else {
			tip
		}
	}

	/// Compute the fee for the specified weight.
	///
	/// This fee is already adjusted by the per block fee adjustment factor and is therefore
	/// the share that the weight contributes to the overall fee of a transaction.
	pub fn weight_to_fee_with_adjustment<Balance>(weight: Weight) -> Balance where
		Balance: UniqueSaturatedFrom<u128>
	{
		let fee = UniqueSaturatedInto::<u128>::unique_saturated_into(Self::weight_to_fee(weight));
		UniqueSaturatedFrom::unique_saturated_from(
			NextFeeMultiplier::get().saturated_multiply_accumulate(fee)
		)
	}

	fn weight_to_fee(weight: Weight) -> BalanceOf<T> {
		// cap the weight to the maximum defined in runtime, otherwise it will be the
		// `Bounded` maximum of its data type, which is not desired.
		let capped_weight = weight.min(<T as frame_system::Trait>::MaximumBlockWeight::get());
		T::WeightToFee::convert(capped_weight)
	}
}

/// Require the transactor pay for themselves and maybe include a tip to gain additional priority
/// in the queue.
#[derive(Encode, Decode, Clone, Eq, PartialEq)]
pub struct ChargeTransactionPayment<T: Trait + Send + Sync>(#[codec(compact)] BalanceOf<T>);

impl<T: Trait + Send + Sync> ChargeTransactionPayment<T> where
	T::Call: Dispatchable<Info=DispatchInfo, PostInfo=PostDispatchInfo>,
	BalanceOf<T>: Send + Sync,
{
	/// utility constructor. Used only in client/factory code.
	pub fn from(fee: BalanceOf<T>) -> Self {
		Self(fee)
	}

	fn withdraw_fee(
		&self,
		who: &T::AccountId,
		info: &DispatchInfoOf<T::Call>,
		len: usize,
	) -> Result<(BalanceOf<T>, Option<NegativeImbalanceOf<T>>), TransactionValidityError> {
		let tip = self.0;
		let fee = Module::<T>::compute_fee(len as u32, info, tip);

		// Only mess with balances if fee is not zero.
		if fee.is_zero() {
			return Ok((fee, None));
		}

		match T::Currency::withdraw(
			who,
			fee,
			if tip.is_zero() {
				WithdrawReason::TransactionPayment.into()
			} else {
				WithdrawReason::TransactionPayment | WithdrawReason::Tip
			},
			ExistenceRequirement::KeepAlive,
		) {
			Ok(imbalance) => Ok((fee, Some(imbalance))),
			Err(_) => Err(InvalidTransaction::Payment.into()),
		}
	}
}

impl<T: Trait + Send + Sync> sp_std::fmt::Debug for ChargeTransactionPayment<T> {
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		write!(f, "ChargeTransactionPayment<{:?}>", self.0)
	}
	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		Ok(())
	}
}

impl<T: Trait + Send + Sync> SignedExtension for ChargeTransactionPayment<T> where
	BalanceOf<T>: Send + Sync + From<u64>,
	T::Call: Dispatchable<Info=DispatchInfo, PostInfo=PostDispatchInfo>,
{
	const IDENTIFIER: &'static str = "ChargeTransactionPayment";
	type AccountId = T::AccountId;
	type Call = T::Call;
	type AdditionalSigned = ();
	type Pre = (BalanceOf<T>, Self::AccountId, Option<NegativeImbalanceOf<T>>);
	fn additional_signed(&self) -> sp_std::result::Result<(), TransactionValidityError> { Ok(()) }

	fn validate(
		&self,
		who: &Self::AccountId,
		_call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> TransactionValidity {
		let (fee, _) = self.withdraw_fee(who, info, len)?;

		let mut r = ValidTransaction::default();
		// NOTE: we probably want to maximize the _fee (of any type) per weight unit_ here, which
		// will be a bit more than setting the priority to tip. For now, this is enough.
		r.priority = fee.saturated_into::<TransactionPriority>();
		Ok(r)
	}

	fn pre_dispatch(
		self,
		who: &Self::AccountId,
		_call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize
	) -> Result<Self::Pre, TransactionValidityError> {
		let (_, imbalance) = self.withdraw_fee(who, info, len)?;
		Ok((self.0, who.clone(), imbalance))
	}

	fn post_dispatch(
		pre: Self::Pre,
		info: &DispatchInfoOf<Self::Call>,
		post_info: &PostDispatchInfoOf<Self::Call>,
		_len: usize,
		_result: &DispatchResult,
	) -> Result<(), TransactionValidityError> {
		let (tip, who, imbalance) = pre;
		if let Some(payed) = imbalance {
			let refund = Module::<T>::weight_to_fee_with_adjustment(post_info.calc_unspent(info));
			let actual_payment = match T::Currency::deposit_into_existing(&who, refund) {
				Ok(refund_imbalance) => {
					// The refund cannot be larger than the up front payed max weight.
					// `PostDispatchInfo::calc_unspent` guards against such a case.
					match payed.offset(refund_imbalance) {
						Ok(actual_payment) => actual_payment,
						Err(_) => return Err(InvalidTransaction::Payment.into()),
					}
				}
				// We do not recreate the account using the refund. The up front payment
				// is gone in that case.
				Err(_) => payed,
			};
			let imbalances = actual_payment.split(tip);
			T::OnTransactionPayment::on_unbalanceds(Some(imbalances.0).into_iter()
				.chain(Some(imbalances.1)));
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use core::num::NonZeroI128;
	use codec::Encode;
	use frame_support::{
		impl_outer_dispatch, impl_outer_origin, parameter_types,
		weights::{DispatchClass, DispatchInfo, PostDispatchInfo, GetDispatchInfo, Weight},
	};
	use pallet_balances::Call as BalancesCall;
	use pallet_transaction_payment_rpc_runtime_api::RuntimeDispatchInfo;
	use sp_core::H256;
	use sp_runtime::{
		testing::{Header, TestXt},
		traits::{BlakeTwo256, IdentityLookup},
		Perbill,
	};
	use std::cell::RefCell;

	const CALL: &<Runtime as frame_system::Trait>::Call =
		&Call::Balances(BalancesCall::transfer(2, 69));

	impl_outer_dispatch! {
		pub enum Call for Runtime where origin: Origin {
			pallet_balances::Balances,
			frame_system::System,
		}
	}

	#[derive(Clone, PartialEq, Eq, Debug)]
	pub struct Runtime;

	use frame_system as system;
	impl_outer_origin!{
		pub enum Origin for Runtime {}
	}

	thread_local! {
		static EXTRINSIC_BASE_WEIGHT: RefCell<u64> = RefCell::new(0);
	}

	pub struct ExtrinsicBaseWeight;
	impl Get<u64> for ExtrinsicBaseWeight {
		fn get() -> u64 { EXTRINSIC_BASE_WEIGHT.with(|v| *v.borrow()) }
	}

	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: Weight = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
	}

	impl frame_system::Trait for Runtime {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Call = Call;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type DbWeight = ();
		type BlockExecutionWeight = ();
		type ExtrinsicBaseWeight = ExtrinsicBaseWeight;
		type MaximumBlockLength = MaximumBlockLength;
		type AvailableBlockRatio = AvailableBlockRatio;
		type Version = ();
		type ModuleToIndex = ();
		type AccountData = pallet_balances::AccountData<u64>;
		type OnNewAccount = ();
		type OnKilledAccount = ();
	}

	parameter_types! {
		pub const ExistentialDeposit: u64 = 1;
	}

	impl pallet_balances::Trait for Runtime {
		type Balance = u64;
		type Event = ();
		type DustRemoval = ();
		type ExistentialDeposit = ExistentialDeposit;
		type AccountStore = System;
	}
	thread_local! {
		static TRANSACTION_BYTE_FEE: RefCell<u64> = RefCell::new(1);
		static WEIGHT_TO_FEE: RefCell<u64> = RefCell::new(1);
	}

	pub struct TransactionByteFee;
	impl Get<u64> for TransactionByteFee {
		fn get() -> u64 { TRANSACTION_BYTE_FEE.with(|v| *v.borrow()) }
	}

	pub struct WeightToFee(u64);
	impl Convert<Weight, u64> for WeightToFee {
		fn convert(t: Weight) -> u64 {
			WEIGHT_TO_FEE.with(|v| *v.borrow() * (t as u64))
		}
	}

	impl Trait for Runtime {
		type Currency = pallet_balances::Module<Runtime>;
		type OnTransactionPayment = ();
		type TransactionByteFee = TransactionByteFee;
		type WeightToFee = WeightToFee;
		type FeeMultiplierUpdate = ();
	}

	type Balances = pallet_balances::Module<Runtime>;
	type System = frame_system::Module<Runtime>;
	type TransactionPayment = Module<Runtime>;

	pub struct ExtBuilder {
		balance_factor: u64,
		base_weight: u64,
		byte_fee: u64,
		weight_to_fee: u64
	}

	impl Default for ExtBuilder {
		fn default() -> Self {
			Self {
				balance_factor: 1,
				base_weight: 0,
				byte_fee: 1,
				weight_to_fee: 1,
			}
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
						(6, 60 * self.balance_factor)
					]
				} else {
					vec![]
				},
			}.assimilate_storage(&mut t).unwrap();
			t.into()
		}
	}

	/// create a transaction info struct from weight. Handy to avoid building the whole struct.
	pub fn info_from_weight(w: Weight) -> DispatchInfo {
		// pays: yes -- class: normal
		DispatchInfo { weight: w, ..Default::default() }
	}

	fn post_info_from_weight(w: Weight) -> PostDispatchInfo {
		PostDispatchInfo { actual_weight: Some(w), }
	}

	fn default_post_info() -> PostDispatchInfo {
		PostDispatchInfo { actual_weight: None, }
	}

	#[test]
	fn signed_extension_transaction_payment_work() {
		ExtBuilder::default()
			.balance_factor(10)
			.base_weight(5)
			.build()
			.execute_with(||
		{
			let len = 10;
			let pre = ChargeTransactionPayment::<Runtime>::from(0)
				.pre_dispatch(&1, CALL, &info_from_weight(5), len)
				.unwrap();
			assert_eq!(Balances::free_balance(1), 100 - 5 - 5 - 10);

			assert!(
				ChargeTransactionPayment::<Runtime>
					::post_dispatch(pre, &info_from_weight(5), &default_post_info(), len, &Ok(()))
					.is_ok()
			);
			assert_eq!(Balances::free_balance(1), 100 - 5 - 5 - 10);

			let pre = ChargeTransactionPayment::<Runtime>::from(5 /* tipped */)
				.pre_dispatch(&2, CALL, &info_from_weight(100), len)
				.unwrap();
			assert_eq!(Balances::free_balance(2), 200 - 5 - 10 - 100 - 5);

			assert!(
				ChargeTransactionPayment::<Runtime>
					::post_dispatch(pre, &info_from_weight(100), &post_info_from_weight(50), len, &Ok(()))
					.is_ok()
			);
			assert_eq!(Balances::free_balance(2), 200 - 5 - 10 - 50 - 5);
		});
	}

	#[test]
	fn signed_extension_transaction_payment_multiplied_refund_works() {
		ExtBuilder::default()
			.balance_factor(10)
			.base_weight(5)
			.build()
			.execute_with(||
		{
			let len = 10;
			NextFeeMultiplier::put(Fixed128::from_rational(1, NonZeroI128::new(2).unwrap()));

			let pre = ChargeTransactionPayment::<Runtime>::from(5 /* tipped */)
				.pre_dispatch(&2, CALL, &info_from_weight(100), len)
				.unwrap();
			// 5 base fee, 3/2 * 10 byte fee, 3/2 * 100 weight fee, 5 tip
			assert_eq!(Balances::free_balance(2), 200 - 5 - 15 - 150 - 5);

			assert!(
				ChargeTransactionPayment::<Runtime>
					::post_dispatch(pre, &info_from_weight(100), &post_info_from_weight(50), len, &Ok(()))
					.is_ok()
			);
			// 75 (3/2 of the returned 50 units of weight ) is refunded
			assert_eq!(Balances::free_balance(2), 200 - 5 - 15 - 75 - 5);
		});
	}

	#[test]
	fn signed_extension_transaction_payment_is_bounded() {
		ExtBuilder::default()
			.balance_factor(1000)
			.byte_fee(0)
			.build()
			.execute_with(||
		{
			// maximum weight possible
			assert!(
				ChargeTransactionPayment::<Runtime>::from(0)
					.pre_dispatch(&1, CALL, &info_from_weight(Weight::max_value()), 10)
					.is_ok()
			);
			// fee will be proportional to what is the actual maximum weight in the runtime.
			assert_eq!(
				Balances::free_balance(&1),
				(10000 - <Runtime as frame_system::Trait>::MaximumBlockWeight::get()) as u64
			);
		});
	}

	#[test]
	fn signed_extension_allows_free_transactions() {
		ExtBuilder::default()
			.base_weight(100)
			.balance_factor(0)
			.build()
			.execute_with(||
		{
			// 1 ain't have a penny.
			assert_eq!(Balances::free_balance(1), 0);

			let len = 100;

			// This is a completely free (and thus wholly insecure/DoS-ridden) transaction.
			let operational_transaction = DispatchInfo {
				weight: 0,
				class: DispatchClass::Operational,
				pays_fee: Pays::No,
			};
			assert!(
				ChargeTransactionPayment::<Runtime>::from(0)
					.validate(&1, CALL, &operational_transaction , len)
					.is_ok()
			);

			// like a InsecureFreeNormal
			let free_transaction = DispatchInfo {
				weight: 0,
				class: DispatchClass::Normal,
				pays_fee: Pays::Yes,
			};
			assert!(
				ChargeTransactionPayment::<Runtime>::from(0)
					.validate(&1, CALL, &free_transaction , len)
					.is_err()
			);
		});
	}

	#[test]
	fn signed_ext_length_fee_is_also_updated_per_congestion() {
		ExtBuilder::default()
			.base_weight(5)
			.balance_factor(10)
			.build()
			.execute_with(||
		{
			// all fees should be x1.5
			NextFeeMultiplier::put(Fixed128::from_rational(1, NonZeroI128::new(2).unwrap()));
			let len = 10;

			assert!(
				ChargeTransactionPayment::<Runtime>::from(10) // tipped
					.pre_dispatch(&1, CALL, &info_from_weight(3), len)
					.is_ok()
			);
			assert_eq!(Balances::free_balance(1), 100 - 10 - 5 - (10 + 3) * 3 / 2);
		})
	}

	#[test]
	fn query_info_works() {
		let call = Call::Balances(BalancesCall::transfer(2, 69));
		let origin = 111111;
		let extra = ();
		let xt = TestXt::new(call, Some((origin, extra)));
		let info  = xt.get_dispatch_info();
		let ext = xt.encode();
		let len = ext.len() as u32;
		ExtBuilder::default()
			.base_weight(5)
			.weight_fee(2)
			.build()
			.execute_with(||
		{
			// all fees should be x1.5
			NextFeeMultiplier::put(Fixed128::from_rational(1, NonZeroI128::new(2).unwrap()));

			assert_eq!(
				TransactionPayment::query_info(xt, len),
				RuntimeDispatchInfo {
					weight: info.weight,
					class: info.class,
					partial_fee:
						5 * 2 /* base * weight_fee */
						+ (
							len as u64 /* len * 1 */
							+ info.weight.min(MaximumBlockWeight::get()) as u64 * 2 /* weight * weight_to_fee */
						) * 3 / 2
				},
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
			.execute_with(||
		{
			// Next fee multiplier is zero
			assert_eq!(NextFeeMultiplier::get(), Fixed128::from_natural(0));

			// Tip only, no fees works
			let dispatch_info = DispatchInfo {
				weight: 0,
				class: DispatchClass::Operational,
				pays_fee: Pays::No,
			};
			assert_eq!(Module::<Runtime>::compute_fee(0, &dispatch_info, 10), 10);
			// No tip, only base fee works
			let dispatch_info = DispatchInfo {
				weight: 0,
				class: DispatchClass::Operational,
				pays_fee: Pays::Yes,
			};
			assert_eq!(Module::<Runtime>::compute_fee(0, &dispatch_info, 0), 100);
			// Tip + base fee works
			assert_eq!(Module::<Runtime>::compute_fee(0, &dispatch_info, 69), 169);
			// Len (byte fee) + base fee works
			assert_eq!(Module::<Runtime>::compute_fee(42, &dispatch_info, 0), 520);
			// Weight fee + base fee works
			let dispatch_info = DispatchInfo {
				weight: 1000,
				class: DispatchClass::Operational,
				pays_fee: Pays::Yes,
			};
			assert_eq!(Module::<Runtime>::compute_fee(0, &dispatch_info, 0), 1100);
		});
	}

	#[test]
	fn compute_fee_works_with_multiplier() {
		ExtBuilder::default()
			.base_weight(100)
			.byte_fee(10)
			.balance_factor(0)
			.build()
			.execute_with(||
		{
			// Add a next fee multiplier
			NextFeeMultiplier::put(Fixed128::from_rational(1, NonZeroI128::new(2).unwrap())); // = 1/2 = .5
			// Base fee is unaffected by multiplier
			let dispatch_info = DispatchInfo {
				weight: 0,
				class: DispatchClass::Operational,
				pays_fee: Pays::Yes,
			};
			assert_eq!(Module::<Runtime>::compute_fee(0, &dispatch_info, 0), 100);

			// Everything works together :)
			let dispatch_info = DispatchInfo {
				weight: 123,
				class: DispatchClass::Operational,
				pays_fee: Pays::Yes,
			};
			// 123 weight, 456 length, 100 base
			// adjustable fee = (123 * 1) + (456 * 10) = 4683
			// adjusted fee = (4683 * .5) + 4683 = 7024.5 -> 7024
			// final fee = 100 + 7024 + 789 tip = 7913
			assert_eq!(Module::<Runtime>::compute_fee(456, &dispatch_info, 789), 7913);
		});
	}

	#[test]
	fn compute_fee_does_not_overflow() {
		ExtBuilder::default()
			.base_weight(100)
			.byte_fee(10)
			.balance_factor(0)
			.build()
			.execute_with(||
		{
			// Overflow is handled
			let dispatch_info = DispatchInfo {
				weight: Weight::max_value(),
				class: DispatchClass::Operational,
				pays_fee: Pays::Yes,
			};
			assert_eq!(
				Module::<Runtime>::compute_fee(
					<u32>::max_value(),
					&dispatch_info,
					<u64>::max_value()
				),
				<u64>::max_value()
			);
		});
	}

	#[test]
	fn refund_does_not_recreate_account() {
		ExtBuilder::default()
			.balance_factor(10)
			.base_weight(5)
			.build()
			.execute_with(||
		{
			let len = 10;
			let pre = ChargeTransactionPayment::<Runtime>::from(5 /* tipped */)
				.pre_dispatch(&2, CALL, &info_from_weight(100), len)
				.unwrap();
			assert_eq!(Balances::free_balance(2), 200 - 5 - 10 - 100 - 5);

			// kill the account between pre and post dispatch
			assert!(Balances::transfer(Some(2).into(), 3, Balances::free_balance(2)).is_ok());
			assert_eq!(Balances::free_balance(2), 0);

			assert!(
				ChargeTransactionPayment::<Runtime>
					::post_dispatch(pre, &info_from_weight(100), &post_info_from_weight(50), len, &Ok(()))
					.is_ok()
			);
			assert_eq!(Balances::free_balance(2), 0);
		});
	}

	#[test]
	fn actual_weight_higher_than_max_refunds_nothing() {
		ExtBuilder::default()
			.balance_factor(10)
			.base_weight(5)
			.build()
			.execute_with(||
		{
			let len = 10;
			let pre = ChargeTransactionPayment::<Runtime>::from(5 /* tipped */)
				.pre_dispatch(&2, CALL, &info_from_weight(100), len)
				.unwrap();
			assert_eq!(Balances::free_balance(2), 200 - 5 - 10 - 100 - 5);

			assert!(
				ChargeTransactionPayment::<Runtime>
					::post_dispatch(pre, &info_from_weight(100), &post_info_from_weight(101), len, &Ok(()))
					.is_ok()
			);
			assert_eq!(Balances::free_balance(2), 200 - 5 - 10 - 100 - 5);
		});
	}
}
