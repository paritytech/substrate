// This file is part of Substrate.

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

//! Dispatch system. Contains a macro for defining runtime modules and
//! generating values representing lazy module function calls.

// Expose the V1 pallet syntax.
#[macro_use]
pub mod decl_module;
pub use decl_module::*;

pub use crate::{
	codec::{
		Codec, Decode, Encode, EncodeAsRef, EncodeLike, HasCompact, Input, MaxEncodedLen, Output,
	},
	scale_info::TypeInfo,
	sp_std::{
		fmt, marker,
		prelude::{Clone, Eq, PartialEq, Vec},
		result,
	},
	traits::{
		CallMetadata, GetCallIndex, GetCallMetadata, GetCallName, GetStorageVersion,
		UnfilteredDispatchable,
	},
};
#[cfg(feature = "std")]
use serde::{Deserialize, Serialize};
use sp_runtime::{
	generic::{CheckedExtrinsic, UncheckedExtrinsic},
	traits::SignedExtension,
};
pub use sp_runtime::{
	traits::Dispatchable, transaction_validity::TransactionPriority, DispatchError, RuntimeDebug,
};
pub use sp_weights::Weight;

/// The return type of a `Dispatchable` in frame. When returned explicitly from
/// a dispatchable function it allows overriding the default `PostDispatchInfo`
/// returned from a dispatch.
pub type DispatchResultWithPostInfo = sp_runtime::DispatchResultWithInfo<PostDispatchInfo>;

/// Unaugmented version of `DispatchResultWithPostInfo` that can be returned from
/// dispatchable functions and is automatically converted to the augmented type. Should be
/// used whenever the `PostDispatchInfo` does not need to be overwritten. As this should
/// be the common case it is the implicit return type when none is specified.
pub type DispatchResult = Result<(), sp_runtime::DispatchError>;

/// The error type contained in a `DispatchResultWithPostInfo`.
pub type DispatchErrorWithPostInfo = sp_runtime::DispatchErrorWithPostInfo<PostDispatchInfo>;

/// Serializable version of pallet dispatchable.
pub trait Callable<T> {
	type RuntimeCall: UnfilteredDispatchable + Codec + Clone + PartialEq + Eq;
}

// dirty hack to work around serde_derive issue
// https://github.com/rust-lang/rust/issues/51331
pub type CallableCallFor<A, R> = <A as Callable<R>>::RuntimeCall;

/// Origin for the System pallet.
#[derive(PartialEq, Eq, Clone, RuntimeDebug, Encode, Decode, TypeInfo, MaxEncodedLen)]
pub enum RawOrigin<AccountId> {
	/// The system itself ordained this dispatch to happen: this is the highest privilege level.
	Root,
	/// It is signed by some public key and we provide the `AccountId`.
	Signed(AccountId),
	/// It is signed by nobody, can be either:
	/// * included and agreed upon by the validators anyway,
	/// * or unsigned transaction validated by a pallet.
	None,
}

impl<AccountId> From<Option<AccountId>> for RawOrigin<AccountId> {
	fn from(s: Option<AccountId>) -> RawOrigin<AccountId> {
		match s {
			Some(who) => RawOrigin::Signed(who),
			None => RawOrigin::None,
		}
	}
}

/// A type that can be used as a parameter in a dispatchable function.
///
/// When using `decl_module` all arguments for call functions must implement this trait.
pub trait Parameter: Codec + EncodeLike + Clone + Eq + fmt::Debug + scale_info::TypeInfo {}
impl<T> Parameter for T where T: Codec + EncodeLike + Clone + Eq + fmt::Debug + scale_info::TypeInfo {}

/// Means of classifying a dispatchable function.
pub trait ClassifyDispatch<T> {
	/// Classify the dispatch function based on input data `target` of type `T`. When implementing
	/// this for a dispatchable, `T` will be a tuple of all arguments given to the function (except
	/// origin).
	fn classify_dispatch(&self, target: T) -> DispatchClass;
}

/// Indicates if dispatch function should pay fees or not.
///
/// If set to `Pays::No`, the block resource limits are applied, yet no fee is deducted.
pub trait PaysFee<T> {
	fn pays_fee(&self, _target: T) -> Pays;
}

/// Explicit enum to denote if a transaction pays fee or not.
#[derive(Clone, Copy, Eq, PartialEq, RuntimeDebug, Encode, Decode, TypeInfo)]
pub enum Pays {
	/// Transactor will pay related fees.
	Yes,
	/// Transactor will NOT pay related fees.
	No,
}

impl Default for Pays {
	fn default() -> Self {
		Self::Yes
	}
}

impl From<Pays> for PostDispatchInfo {
	fn from(pays_fee: Pays) -> Self {
		Self { actual_weight: None, pays_fee }
	}
}

/// A generalized group of dispatch types.
///
/// NOTE whenever upgrading the enum make sure to also update
/// [DispatchClass::all] and [DispatchClass::non_mandatory] helper functions.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[derive(PartialEq, Eq, Clone, Copy, Encode, Decode, RuntimeDebug, TypeInfo)]
pub enum DispatchClass {
	/// A normal dispatch.
	Normal,
	/// An operational dispatch.
	Operational,
	/// A mandatory dispatch. These kinds of dispatch are always included regardless of their
	/// weight, therefore it is critical that they are separately validated to ensure that a
	/// malicious validator cannot craft a valid but impossibly heavy block. Usually this just
	/// means ensuring that the extrinsic can only be included once and that it is always very
	/// light.
	///
	/// Do *NOT* use it for extrinsics that can be heavy.
	///
	/// The only real use case for this is inherent extrinsics that are required to execute in a
	/// block for the block to be valid, and it solves the issue in the case that the block
	/// initialization is sufficiently heavy to mean that those inherents do not fit into the
	/// block. Essentially, we assume that in these exceptional circumstances, it is better to
	/// allow an overweight block to be created than to not allow any block at all to be created.
	Mandatory,
}

impl Default for DispatchClass {
	fn default() -> Self {
		Self::Normal
	}
}

impl DispatchClass {
	/// Returns an array containing all dispatch classes.
	pub fn all() -> &'static [DispatchClass] {
		&[DispatchClass::Normal, DispatchClass::Operational, DispatchClass::Mandatory]
	}

	/// Returns an array of all dispatch classes except `Mandatory`.
	pub fn non_mandatory() -> &'static [DispatchClass] {
		&[DispatchClass::Normal, DispatchClass::Operational]
	}
}

/// A trait that represents one or many values of given type.
///
/// Useful to accept as parameter type to let the caller pass either a single value directly
/// or an iterator.
pub trait OneOrMany<T> {
	/// The iterator type.
	type Iter: Iterator<Item = T>;
	/// Convert this item into an iterator.
	fn into_iter(self) -> Self::Iter;
}

impl OneOrMany<DispatchClass> for DispatchClass {
	type Iter = sp_std::iter::Once<DispatchClass>;
	fn into_iter(self) -> Self::Iter {
		sp_std::iter::once(self)
	}
}

impl<'a> OneOrMany<DispatchClass> for &'a [DispatchClass] {
	type Iter = sp_std::iter::Cloned<sp_std::slice::Iter<'a, DispatchClass>>;
	fn into_iter(self) -> Self::Iter {
		self.iter().cloned()
	}
}

/// A bundle of static information collected from the `#[pallet::weight]` attributes.
#[derive(Clone, Copy, Eq, PartialEq, Default, RuntimeDebug, Encode, Decode, TypeInfo)]
pub struct DispatchInfo {
	/// Weight of this transaction.
	pub weight: Weight,
	/// Class of this transaction.
	pub class: DispatchClass,
	/// Does this transaction pay fees.
	pub pays_fee: Pays,
}

/// A `Dispatchable` function (aka transaction) that can carry some static information along with
/// it, using the `#[pallet::weight]` attribute.
pub trait GetDispatchInfo {
	/// Return a `DispatchInfo`, containing relevant information of this dispatch.
	///
	/// This is done independently of its encoded size.
	fn get_dispatch_info(&self) -> DispatchInfo;
}

impl GetDispatchInfo for () {
	fn get_dispatch_info(&self) -> DispatchInfo {
		DispatchInfo::default()
	}
}

/// Extract the actual weight from a dispatch result if any or fall back to the default weight.
pub fn extract_actual_weight(result: &DispatchResultWithPostInfo, info: &DispatchInfo) -> Weight {
	match result {
		Ok(post_info) => post_info,
		Err(err) => &err.post_info,
	}
	.calc_actual_weight(info)
}

/// Extract the actual pays_fee from a dispatch result if any or fall back to the default weight.
pub fn extract_actual_pays_fee(result: &DispatchResultWithPostInfo, info: &DispatchInfo) -> Pays {
	match result {
		Ok(post_info) => post_info,
		Err(err) => &err.post_info,
	}
	.pays_fee(info)
}

/// Weight information that is only available post dispatch.
/// NOTE: This can only be used to reduce the weight or fee, not increase it.
#[derive(Clone, Copy, Eq, PartialEq, Default, RuntimeDebug, Encode, Decode, TypeInfo)]
pub struct PostDispatchInfo {
	/// Actual weight consumed by a call or `None` which stands for the worst case static weight.
	pub actual_weight: Option<Weight>,
	/// Whether this transaction should pay fees when all is said and done.
	pub pays_fee: Pays,
}

impl PostDispatchInfo {
	/// Calculate how much (if any) weight was not used by the `Dispatchable`.
	pub fn calc_unspent(&self, info: &DispatchInfo) -> Weight {
		info.weight - self.calc_actual_weight(info)
	}

	/// Calculate how much weight was actually spent by the `Dispatchable`.
	pub fn calc_actual_weight(&self, info: &DispatchInfo) -> Weight {
		if let Some(actual_weight) = self.actual_weight {
			actual_weight.min(info.weight)
		} else {
			info.weight
		}
	}

	/// Determine if user should actually pay fees at the end of the dispatch.
	pub fn pays_fee(&self, info: &DispatchInfo) -> Pays {
		// If they originally were not paying fees, or the post dispatch info
		// says they should not pay fees, then they don't pay fees.
		// This is because the pre dispatch information must contain the
		// worst case for weight and fees paid.
		if info.pays_fee == Pays::No || self.pays_fee == Pays::No {
			Pays::No
		} else {
			// Otherwise they pay.
			Pays::Yes
		}
	}
}

impl From<()> for PostDispatchInfo {
	fn from(_: ()) -> Self {
		Self { actual_weight: None, pays_fee: Default::default() }
	}
}

impl sp_runtime::traits::Printable for PostDispatchInfo {
	fn print(&self) {
		"actual_weight=".print();
		match self.actual_weight {
			Some(weight) => weight.print(),
			None => "max-weight".print(),
		};
		"pays_fee=".print();
		match self.pays_fee {
			Pays::Yes => "Yes".print(),
			Pays::No => "No".print(),
		}
	}
}

/// Allows easy conversion from `DispatchError` to `DispatchErrorWithPostInfo` for dispatchables
/// that want to return a custom a posterior weight on error.
pub trait WithPostDispatchInfo {
	/// Call this on your modules custom errors type in order to return a custom weight on error.
	///
	/// # Example
	///
	/// ```ignore
	/// let who = ensure_signed(origin).map_err(|e| e.with_weight(Weight::from_parts(100, 0)))?;
	/// ensure!(who == me, Error::<T>::NotMe.with_weight(200_000));
	/// ```
	fn with_weight(self, actual_weight: Weight) -> DispatchErrorWithPostInfo;
}

impl<T> WithPostDispatchInfo for T
where
	T: Into<DispatchError>,
{
	fn with_weight(self, actual_weight: Weight) -> DispatchErrorWithPostInfo {
		DispatchErrorWithPostInfo {
			post_info: PostDispatchInfo {
				actual_weight: Some(actual_weight),
				pays_fee: Default::default(),
			},
			error: self.into(),
		}
	}
}

/// Implementation for unchecked extrinsic.
impl<Address, Call, Signature, Extra> GetDispatchInfo
	for UncheckedExtrinsic<Address, Call, Signature, Extra>
where
	Call: GetDispatchInfo,
	Extra: SignedExtension,
{
	fn get_dispatch_info(&self) -> DispatchInfo {
		self.function.get_dispatch_info()
	}
}

/// Implementation for checked extrinsic.
impl<AccountId, Call, Extra> GetDispatchInfo for CheckedExtrinsic<AccountId, Call, Extra>
where
	Call: GetDispatchInfo,
{
	fn get_dispatch_info(&self) -> DispatchInfo {
		self.function.get_dispatch_info()
	}
}

/// Implementation for test extrinsic.
#[cfg(feature = "std")]
impl<Call: Encode + GetDispatchInfo, Extra: Encode> GetDispatchInfo
	for sp_runtime::testing::TestXt<Call, Extra>
{
	fn get_dispatch_info(&self) -> DispatchInfo {
		// for testing: weight == size.
		DispatchInfo {
			weight: Weight::from_parts(self.encode().len() as _, 0),
			pays_fee: Pays::Yes,
			class: self.call.get_dispatch_info().class,
		}
	}
}

/// A struct holding value for each `DispatchClass`.
#[derive(Clone, Eq, PartialEq, Default, RuntimeDebug, Encode, Decode, TypeInfo, MaxEncodedLen)]
pub struct PerDispatchClass<T> {
	/// Value for `Normal` extrinsics.
	normal: T,
	/// Value for `Operational` extrinsics.
	operational: T,
	/// Value for `Mandatory` extrinsics.
	mandatory: T,
}

impl<T> PerDispatchClass<T> {
	/// Create new `PerDispatchClass` with the same value for every class.
	pub fn new(val: impl Fn(DispatchClass) -> T) -> Self {
		Self {
			normal: val(DispatchClass::Normal),
			operational: val(DispatchClass::Operational),
			mandatory: val(DispatchClass::Mandatory),
		}
	}

	/// Get a mutable reference to current value of given class.
	pub fn get_mut(&mut self, class: DispatchClass) -> &mut T {
		match class {
			DispatchClass::Operational => &mut self.operational,
			DispatchClass::Normal => &mut self.normal,
			DispatchClass::Mandatory => &mut self.mandatory,
		}
	}

	/// Get current value for given class.
	pub fn get(&self, class: DispatchClass) -> &T {
		match class {
			DispatchClass::Normal => &self.normal,
			DispatchClass::Operational => &self.operational,
			DispatchClass::Mandatory => &self.mandatory,
		}
	}
}

impl<T: Clone> PerDispatchClass<T> {
	/// Set the value of given class.
	pub fn set(&mut self, new: T, class: impl OneOrMany<DispatchClass>) {
		for class in class.into_iter() {
			*self.get_mut(class) = new.clone();
		}
	}
}

impl PerDispatchClass<Weight> {
	/// Returns the total weight consumed by all extrinsics in the block.
	///
	/// Saturates on overflow.
	pub fn total(&self) -> Weight {
		let mut sum = Weight::zero();
		for class in DispatchClass::all() {
			sum.saturating_accrue(*self.get(*class));
		}
		sum
	}

	/// Add some weight to the given class. Saturates at the numeric bounds.
	pub fn add(mut self, weight: Weight, class: DispatchClass) -> Self {
		self.accrue(weight, class);
		self
	}

	/// Increase the weight of the given class. Saturates at the numeric bounds.
	pub fn accrue(&mut self, weight: Weight, class: DispatchClass) {
		self.get_mut(class).saturating_accrue(weight);
	}

	/// Try to increase the weight of the given class. Saturates at the numeric bounds.
	pub fn checked_accrue(&mut self, weight: Weight, class: DispatchClass) -> Result<(), ()> {
		self.get_mut(class).checked_accrue(weight).ok_or(())
	}

	/// Reduce the weight of the given class. Saturates at the numeric bounds.
	pub fn reduce(&mut self, weight: Weight, class: DispatchClass) {
		self.get_mut(class).saturating_reduce(weight);
	}
}

/// Means of weighing some particular kind of data (`T`).
pub trait WeighData<T> {
	/// Weigh the data `T` given by `target`. When implementing this for a dispatchable, `T` will be
	/// a tuple of all arguments given to the function (except origin).
	fn weigh_data(&self, target: T) -> Weight;
}

impl<T> WeighData<T> for Weight {
	fn weigh_data(&self, _: T) -> Weight {
		return *self
	}
}

impl<T> PaysFee<T> for (Weight, DispatchClass, Pays) {
	fn pays_fee(&self, _: T) -> Pays {
		self.2
	}
}

impl<T> WeighData<T> for (Weight, DispatchClass) {
	fn weigh_data(&self, args: T) -> Weight {
		return self.0.weigh_data(args)
	}
}

impl<T> WeighData<T> for (Weight, DispatchClass, Pays) {
	fn weigh_data(&self, args: T) -> Weight {
		return self.0.weigh_data(args)
	}
}

impl<T> ClassifyDispatch<T> for (Weight, DispatchClass) {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		self.1
	}
}

impl<T> PaysFee<T> for (Weight, DispatchClass) {
	fn pays_fee(&self, _: T) -> Pays {
		Pays::Yes
	}
}

impl<T> WeighData<T> for (Weight, Pays) {
	fn weigh_data(&self, args: T) -> Weight {
		return self.0.weigh_data(args)
	}
}

impl<T> ClassifyDispatch<T> for (Weight, Pays) {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		DispatchClass::Normal
	}
}

impl<T> PaysFee<T> for (Weight, Pays) {
	fn pays_fee(&self, _: T) -> Pays {
		self.1
	}
}

impl From<(Option<Weight>, Pays)> for PostDispatchInfo {
	fn from(post_weight_info: (Option<Weight>, Pays)) -> Self {
		let (actual_weight, pays_fee) = post_weight_info;
		Self { actual_weight, pays_fee }
	}
}

impl From<Option<Weight>> for PostDispatchInfo {
	fn from(actual_weight: Option<Weight>) -> Self {
		Self { actual_weight, pays_fee: Default::default() }
	}
}

impl<T> ClassifyDispatch<T> for Weight {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		DispatchClass::Normal
	}
}

impl<T> PaysFee<T> for Weight {
	fn pays_fee(&self, _: T) -> Pays {
		Pays::Yes
	}
}

impl<T> ClassifyDispatch<T> for (Weight, DispatchClass, Pays) {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		self.1
	}
}

// TODO: Eventually remove these

impl<T> ClassifyDispatch<T> for u64 {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		DispatchClass::Normal
	}
}

impl<T> PaysFee<T> for u64 {
	fn pays_fee(&self, _: T) -> Pays {
		Pays::Yes
	}
}

impl<T> WeighData<T> for u64 {
	fn weigh_data(&self, _: T) -> Weight {
		return Weight::from_parts(*self, 0)
	}
}

impl<T> WeighData<T> for (u64, DispatchClass, Pays) {
	fn weigh_data(&self, args: T) -> Weight {
		return self.0.weigh_data(args)
	}
}

impl<T> ClassifyDispatch<T> for (u64, DispatchClass, Pays) {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		self.1
	}
}

impl<T> PaysFee<T> for (u64, DispatchClass, Pays) {
	fn pays_fee(&self, _: T) -> Pays {
		self.2
	}
}

impl<T> WeighData<T> for (u64, DispatchClass) {
	fn weigh_data(&self, args: T) -> Weight {
		return self.0.weigh_data(args)
	}
}

impl<T> ClassifyDispatch<T> for (u64, DispatchClass) {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		self.1
	}
}

impl<T> PaysFee<T> for (u64, DispatchClass) {
	fn pays_fee(&self, _: T) -> Pays {
		Pays::Yes
	}
}

impl<T> WeighData<T> for (u64, Pays) {
	fn weigh_data(&self, args: T) -> Weight {
		return self.0.weigh_data(args)
	}
}

impl<T> ClassifyDispatch<T> for (u64, Pays) {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		DispatchClass::Normal
	}
}

impl<T> PaysFee<T> for (u64, Pays) {
	fn pays_fee(&self, _: T) -> Pays {
		self.1
	}
}

// END TODO

#[cfg(test)]
// Do not complain about unused `dispatch` and `dispatch_aux`.
#[allow(dead_code)]
mod tests {
	use super::*;
	use crate::{
		dispatch::{DispatchClass, DispatchInfo, Pays},
		metadata_ir::*,
		traits::{
			CallerTrait, CrateVersion, Get, GetCallName, IntegrityTest, OnFinalize, OnIdle,
			OnInitialize, OnRuntimeUpgrade, PalletInfo,
		},
	};
	use sp_weights::{RuntimeDbWeight, Weight};

	pub trait Config: system::Config + Sized
	where
		Self::AccountId: From<u32>,
	{
	}

	pub mod system {
		use super::*;

		pub trait Config: 'static {
			type AccountId;
			type RuntimeCall;
			type BaseCallFilter;
			type RuntimeOrigin: crate::traits::OriginTrait<Call = Self::RuntimeCall>;
			type BlockNumber: Into<u32>;
			type PalletInfo: crate::traits::PalletInfo;
			type DbWeight: Get<RuntimeDbWeight>;
		}

		pub use super::super::RawOrigin;

		pub type Origin<T> = RawOrigin<<T as Config>::AccountId>;
	}

	decl_module! {
		pub struct Module<T: Config> for enum Call where origin: T::RuntimeOrigin, system = system, T::AccountId: From<u32> {
			/// Hi, this is a comment.
			#[weight = 0]
			fn aux_0(_origin) -> DispatchResult { unreachable!() }

			#[weight = 0]
			fn aux_1(_origin, #[compact] _data: u32,) -> DispatchResult { unreachable!() }

			#[weight = 0]
			fn aux_2(_origin, _data: i32, _data2: String) -> DispatchResult { unreachable!() }

			#[weight = 3]
			fn aux_3(_origin) -> DispatchResult { unreachable!() }

			#[weight = 0]
			fn aux_4(_origin, _data: i32) -> DispatchResult { unreachable!() }

			#[weight = 0]
			fn aux_5(_origin, _data: i32, #[compact] _data2: u32,) -> DispatchResult { unreachable!() }

			#[weight = (5, DispatchClass::Operational)]
			fn operational(_origin) { unreachable!() }

			fn on_initialize(n: T::BlockNumber,) -> Weight { if n.into() == 42 { panic!("on_initialize") } Weight::from_parts(7, 0) }
			fn on_idle(n: T::BlockNumber, remaining_weight: Weight,) -> Weight {
				if n.into() == 42 || remaining_weight == Weight::from_parts(42, 0)  { panic!("on_idle") }
				Weight::from_parts(7, 0)
			}
			fn on_finalize(n: T::BlockNumber,) { if n.into() == 42 { panic!("on_finalize") } }
			fn on_runtime_upgrade() -> Weight { Weight::from_parts(10, 0) }
			fn offchain_worker() {}
			/// Some doc
			fn integrity_test() { panic!("integrity_test") }
		}
	}

	#[derive(Eq, PartialEq, Clone, crate::RuntimeDebug, scale_info::TypeInfo)]
	pub struct TraitImpl {}
	impl Config for TraitImpl {}

	type Test = Module<TraitImpl>;

	impl PalletInfo for TraitImpl {
		fn index<P: 'static>() -> Option<usize> {
			let type_id = sp_std::any::TypeId::of::<P>();
			if type_id == sp_std::any::TypeId::of::<Test>() {
				return Some(0)
			}

			None
		}
		fn name<P: 'static>() -> Option<&'static str> {
			let type_id = sp_std::any::TypeId::of::<P>();
			if type_id == sp_std::any::TypeId::of::<Test>() {
				return Some("Test")
			}

			None
		}
		fn module_name<P: 'static>() -> Option<&'static str> {
			let type_id = sp_std::any::TypeId::of::<P>();
			if type_id == sp_std::any::TypeId::of::<Test>() {
				return Some("tests")
			}

			None
		}
		fn crate_version<P: 'static>() -> Option<CrateVersion> {
			let type_id = sp_std::any::TypeId::of::<P>();
			if type_id == sp_std::any::TypeId::of::<Test>() {
				return Some(frame_support::crate_to_crate_version!())
			}

			None
		}
	}

	#[derive(
		TypeInfo, crate::RuntimeDebug, Eq, PartialEq, Clone, Encode, Decode, MaxEncodedLen,
	)]
	pub struct OuterOrigin;

	impl From<RawOrigin<<TraitImpl as system::Config>::AccountId>> for OuterOrigin {
		fn from(_: RawOrigin<<TraitImpl as system::Config>::AccountId>) -> Self {
			unimplemented!("Not required in tests!")
		}
	}

	impl CallerTrait<<TraitImpl as system::Config>::AccountId> for OuterOrigin {
		fn into_system(self) -> Option<RawOrigin<<TraitImpl as system::Config>::AccountId>> {
			unimplemented!("Not required in tests!")
		}

		fn as_system_ref(&self) -> Option<&RawOrigin<<TraitImpl as system::Config>::AccountId>> {
			unimplemented!("Not required in tests!")
		}
	}

	impl crate::traits::OriginTrait for OuterOrigin {
		type Call = <TraitImpl as system::Config>::RuntimeCall;
		type PalletsOrigin = OuterOrigin;
		type AccountId = <TraitImpl as system::Config>::AccountId;

		fn add_filter(&mut self, _filter: impl Fn(&Self::Call) -> bool + 'static) {
			unimplemented!("Not required in tests!")
		}

		fn reset_filter(&mut self) {
			unimplemented!("Not required in tests!")
		}

		fn set_caller_from(&mut self, _other: impl Into<Self>) {
			unimplemented!("Not required in tests!")
		}

		fn filter_call(&self, _call: &Self::Call) -> bool {
			unimplemented!("Not required in tests!")
		}

		fn caller(&self) -> &Self::PalletsOrigin {
			unimplemented!("Not required in tests!")
		}

		fn into_caller(self) -> Self::PalletsOrigin {
			unimplemented!("Not required in tests!")
		}

		fn try_with_caller<R>(
			self,
			_f: impl FnOnce(Self::PalletsOrigin) -> Result<R, Self::PalletsOrigin>,
		) -> Result<R, Self> {
			unimplemented!("Not required in tests!")
		}

		fn none() -> Self {
			unimplemented!("Not required in tests!")
		}
		fn root() -> Self {
			unimplemented!("Not required in tests!")
		}
		fn signed(_by: <TraitImpl as system::Config>::AccountId) -> Self {
			unimplemented!("Not required in tests!")
		}
		fn as_signed(self) -> Option<Self::AccountId> {
			unimplemented!("Not required in tests!")
		}
		fn as_system_ref(&self) -> Option<&RawOrigin<Self::AccountId>> {
			unimplemented!("Not required in tests!")
		}
	}

	impl system::Config for TraitImpl {
		type RuntimeOrigin = OuterOrigin;
		type AccountId = u32;
		type RuntimeCall = ();
		type BaseCallFilter = frame_support::traits::Everything;
		type BlockNumber = u32;
		type PalletInfo = Self;
		type DbWeight = ();
	}

	#[test]
	fn module_json_metadata() {
		let metadata = Module::<TraitImpl>::call_functions();
		let expected_metadata =
			PalletCallMetadataIR { ty: scale_info::meta_type::<Call<TraitImpl>>() };
		assert_eq!(expected_metadata, metadata);
	}

	#[test]
	fn compact_attr() {
		let call: Call<TraitImpl> = Call::aux_1 { _data: 1 };
		let encoded = call.encode();
		assert_eq!(2, encoded.len());
		assert_eq!(vec![1, 4], encoded);

		let call: Call<TraitImpl> = Call::aux_5 { _data: 1, _data2: 2 };
		let encoded = call.encode();
		assert_eq!(6, encoded.len());
		assert_eq!(vec![5, 1, 0, 0, 0, 8], encoded);
	}

	#[test]
	fn encode_is_correct_and_decode_works() {
		let call: Call<TraitImpl> = Call::aux_0 {};
		let encoded = call.encode();
		assert_eq!(vec![0], encoded);
		let decoded = Call::<TraitImpl>::decode(&mut &encoded[..]).unwrap();
		assert_eq!(decoded, call);

		let call: Call<TraitImpl> = Call::aux_2 { _data: 32, _data2: "hello".into() };
		let encoded = call.encode();
		assert_eq!(vec![2, 32, 0, 0, 0, 20, 104, 101, 108, 108, 111], encoded);
		let decoded = Call::<TraitImpl>::decode(&mut &encoded[..]).unwrap();
		assert_eq!(decoded, call);
	}

	#[test]
	#[should_panic(expected = "on_initialize")]
	fn on_initialize_should_work_1() {
		<Module<TraitImpl> as OnInitialize<u32>>::on_initialize(42);
	}

	#[test]
	fn on_initialize_should_work_2() {
		assert_eq!(
			<Module<TraitImpl> as OnInitialize<u32>>::on_initialize(10),
			Weight::from_parts(7, 0)
		);
	}

	#[test]
	#[should_panic(expected = "on_idle")]
	fn on_idle_should_work_1() {
		<Module<TraitImpl> as OnIdle<u32>>::on_idle(42, Weight::from_parts(9, 0));
	}

	#[test]
	#[should_panic(expected = "on_idle")]
	fn on_idle_should_work_2() {
		<Module<TraitImpl> as OnIdle<u32>>::on_idle(9, Weight::from_parts(42, 0));
	}

	#[test]
	fn on_idle_should_work_3() {
		assert_eq!(
			<Module<TraitImpl> as OnIdle<u32>>::on_idle(10, Weight::from_parts(11, 0)),
			Weight::from_parts(7, 0)
		);
	}

	#[test]
	#[should_panic(expected = "on_finalize")]
	fn on_finalize_should_work() {
		<Module<TraitImpl> as OnFinalize<u32>>::on_finalize(42);
	}

	#[test]
	fn on_runtime_upgrade_should_work() {
		sp_io::TestExternalities::default().execute_with(|| {
			assert_eq!(
				<Module<TraitImpl> as OnRuntimeUpgrade>::on_runtime_upgrade(),
				Weight::from_parts(10, 0)
			)
		});
	}

	#[test]
	fn weight_should_attach_to_call_enum() {
		// operational.
		assert_eq!(
			Call::<TraitImpl>::operational {}.get_dispatch_info(),
			DispatchInfo {
				weight: Weight::from_parts(5, 0),
				class: DispatchClass::Operational,
				pays_fee: Pays::Yes
			},
		);
		// custom basic
		assert_eq!(
			Call::<TraitImpl>::aux_3 {}.get_dispatch_info(),
			DispatchInfo {
				weight: Weight::from_parts(3, 0),
				class: DispatchClass::Normal,
				pays_fee: Pays::Yes
			},
		);
	}

	#[test]
	fn call_name() {
		let name = Call::<TraitImpl>::aux_3 {}.get_call_name();
		assert_eq!("aux_3", name);
	}

	#[test]
	fn get_call_names() {
		let call_names = Call::<TraitImpl>::get_call_names();
		assert_eq!(
			["aux_0", "aux_1", "aux_2", "aux_3", "aux_4", "aux_5", "operational"],
			call_names
		);
	}

	#[test]
	#[should_panic(expected = "integrity_test")]
	fn integrity_test_should_work() {
		<Module<TraitImpl> as IntegrityTest>::integrity_test();
	}

	#[test]
	fn test_new_call_variant() {
		Call::<TraitImpl>::new_call_variant_aux_0();
	}

	pub fn from_actual_ref_time(ref_time: Option<u64>) -> PostDispatchInfo {
		PostDispatchInfo {
			actual_weight: ref_time.map(|t| Weight::from_all(t)),
			pays_fee: Default::default(),
		}
	}

	pub fn from_post_weight_info(ref_time: Option<u64>, pays_fee: Pays) -> PostDispatchInfo {
		PostDispatchInfo { actual_weight: ref_time.map(|t| Weight::from_all(t)), pays_fee }
	}
}

#[cfg(test)]
// Do not complain about unused `dispatch` and `dispatch_aux`.
#[allow(dead_code)]
mod weight_tests {
	use super::{tests::*, *};
	use sp_core::parameter_types;
	use sp_runtime::{generic, traits::BlakeTwo256};
	use sp_weights::RuntimeDbWeight;

	pub use self::frame_system::{Call, Config, Pallet};

	#[crate::pallet(dev_mode)]
	pub mod frame_system {
		use super::{frame_system, frame_system::pallet_prelude::*};
		pub use crate::dispatch::RawOrigin;
		use crate::pallet_prelude::*;

		#[pallet::pallet]
		pub struct Pallet<T>(PhantomData<T>);

		#[pallet::config]
		#[pallet::disable_frame_system_supertrait_check]
		pub trait Config: 'static {
			type BlockNumber: Parameter + Default + MaxEncodedLen;
			type AccountId;
			type Balance;
			type BaseCallFilter: crate::traits::Contains<Self::RuntimeCall>;
			type RuntimeOrigin;
			type RuntimeCall;
			type PalletInfo: crate::traits::PalletInfo;
			type DbWeight: Get<crate::weights::RuntimeDbWeight>;
		}

		#[pallet::error]
		pub enum Error<T> {
			/// Required by construct_runtime
			CallFiltered,
		}

		#[pallet::origin]
		pub type Origin<T> = RawOrigin<<T as Config>::AccountId>;

		#[pallet::call]
		impl<T: Config> Pallet<T> {
			// no arguments, fixed weight
			#[pallet::weight(1000)]
			pub fn f00(_origin: OriginFor<T>) -> DispatchResult {
				unimplemented!();
			}

			#[pallet::weight((1000, DispatchClass::Mandatory))]
			pub fn f01(_origin: OriginFor<T>) -> DispatchResult {
				unimplemented!();
			}

			#[pallet::weight((1000, Pays::No))]
			pub fn f02(_origin: OriginFor<T>) -> DispatchResult {
				unimplemented!();
			}

			#[pallet::weight((1000, DispatchClass::Operational, Pays::No))]
			pub fn f03(_origin: OriginFor<T>) -> DispatchResult {
				unimplemented!();
			}

			// weight = a x 10 + b
			#[pallet::weight(((_a * 10 + _eb * 1) as u64, DispatchClass::Normal, Pays::Yes))]
			pub fn f11(_origin: OriginFor<T>, _a: u32, _eb: u32) -> DispatchResult {
				unimplemented!();
			}

			#[pallet::weight((0, DispatchClass::Operational, Pays::Yes))]
			pub fn f12(_origin: OriginFor<T>, _a: u32, _eb: u32) -> DispatchResult {
				unimplemented!();
			}

			#[pallet::weight(T::DbWeight::get().reads(3) + T::DbWeight::get().writes(2) + Weight::from_all(10_000))]
			pub fn f20(_origin: OriginFor<T>) -> DispatchResult {
				unimplemented!();
			}

			#[pallet::weight(T::DbWeight::get().reads_writes(6, 5) + Weight::from_all(40_000))]
			pub fn f21(_origin: OriginFor<T>) -> DispatchResult {
				unimplemented!();
			}
		}

		pub mod pallet_prelude {
			pub type OriginFor<T> = <T as super::Config>::RuntimeOrigin;
		}
	}

	type BlockNumber = u32;
	type AccountId = u32;
	type Balance = u32;
	type Header = generic::Header<BlockNumber, BlakeTwo256>;
	type UncheckedExtrinsic = generic::UncheckedExtrinsic<u32, RuntimeCall, (), ()>;
	type Block = generic::Block<Header, UncheckedExtrinsic>;

	crate::construct_runtime!(
		pub enum Runtime
		where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic,
		{
			System: self::frame_system,
		}
	);

	parameter_types! {
		pub const DbWeight: RuntimeDbWeight = RuntimeDbWeight {
			read: 100,
			write: 1000,
		};
	}

	impl Config for Runtime {
		type BlockNumber = BlockNumber;
		type AccountId = AccountId;
		type Balance = Balance;
		type BaseCallFilter = crate::traits::Everything;
		type RuntimeOrigin = RuntimeOrigin;
		type RuntimeCall = RuntimeCall;
		type DbWeight = DbWeight;
		type PalletInfo = PalletInfo;
	}

	#[test]
	fn weights_are_correct() {
		// #[pallet::weight(1000)]
		let info = Call::<Runtime>::f00 {}.get_dispatch_info();
		assert_eq!(info.weight, Weight::from_parts(1000, 0));
		assert_eq!(info.class, DispatchClass::Normal);
		assert_eq!(info.pays_fee, Pays::Yes);

		// #[pallet::weight((1000, DispatchClass::Mandatory))]
		let info = Call::<Runtime>::f01 {}.get_dispatch_info();
		assert_eq!(info.weight, Weight::from_parts(1000, 0));
		assert_eq!(info.class, DispatchClass::Mandatory);
		assert_eq!(info.pays_fee, Pays::Yes);

		// #[pallet::weight((1000, Pays::No))]
		let info = Call::<Runtime>::f02 {}.get_dispatch_info();
		assert_eq!(info.weight, Weight::from_parts(1000, 0));
		assert_eq!(info.class, DispatchClass::Normal);
		assert_eq!(info.pays_fee, Pays::No);

		// #[pallet::weight((1000, DispatchClass::Operational, Pays::No))]
		let info = Call::<Runtime>::f03 {}.get_dispatch_info();
		assert_eq!(info.weight, Weight::from_parts(1000, 0));
		assert_eq!(info.class, DispatchClass::Operational);
		assert_eq!(info.pays_fee, Pays::No);

		// #[pallet::weight(((_a * 10 + _eb * 1) as u64, DispatchClass::Normal, Pays::Yes))]
		let info = Call::<Runtime>::f11 { a: 13, eb: 20 }.get_dispatch_info();
		assert_eq!(info.weight, Weight::from_parts(150, 0)); // 13*10 + 20
		assert_eq!(info.class, DispatchClass::Normal);
		assert_eq!(info.pays_fee, Pays::Yes);

		// #[pallet::weight((0, DispatchClass::Operational, Pays::Yes))]
		let info = Call::<Runtime>::f12 { a: 10, eb: 20 }.get_dispatch_info();
		assert_eq!(info.weight, Weight::zero());
		assert_eq!(info.class, DispatchClass::Operational);
		assert_eq!(info.pays_fee, Pays::Yes);

		// #[pallet::weight(T::DbWeight::get().reads(3) + T::DbWeight::get().writes(2) +
		// Weight::from_all(10_000))]
		let info = Call::<Runtime>::f20 {}.get_dispatch_info();
		assert_eq!(info.weight, Weight::from_parts(12300, 10000)); // 100*3 + 1000*2 + 10_1000
		assert_eq!(info.class, DispatchClass::Normal);
		assert_eq!(info.pays_fee, Pays::Yes);

		// #[pallet::weight(T::DbWeight::get().reads_writes(6, 5) + Weight::from_all(40_000))]
		let info = Call::<Runtime>::f21 {}.get_dispatch_info();
		assert_eq!(info.weight, Weight::from_parts(45600, 40000)); // 100*6 + 1000*5 + 40_1000
		assert_eq!(info.class, DispatchClass::Normal);
		assert_eq!(info.pays_fee, Pays::Yes);
	}

	#[test]
	fn extract_actual_weight_works() {
		let pre = DispatchInfo { weight: Weight::from_parts(1000, 0), ..Default::default() };
		assert_eq!(
			extract_actual_weight(&Ok(from_actual_ref_time(Some(7))), &pre),
			Weight::from_parts(7, 0)
		);
		assert_eq!(
			extract_actual_weight(&Ok(from_actual_ref_time(Some(1000))), &pre),
			Weight::from_parts(1000, 0)
		);
		assert_eq!(
			extract_actual_weight(
				&Err(DispatchError::BadOrigin.with_weight(Weight::from_parts(9, 0))),
				&pre
			),
			Weight::from_parts(9, 0)
		);
	}

	#[test]
	fn extract_actual_weight_caps_at_pre_weight() {
		let pre = DispatchInfo { weight: Weight::from_parts(1000, 0), ..Default::default() };
		assert_eq!(
			extract_actual_weight(&Ok(from_actual_ref_time(Some(1250))), &pre),
			Weight::from_parts(1000, 0)
		);
		assert_eq!(
			extract_actual_weight(
				&Err(DispatchError::BadOrigin.with_weight(Weight::from_parts(1300, 0))),
				&pre
			),
			Weight::from_parts(1000, 0),
		);
	}

	#[test]
	fn extract_actual_pays_fee_works() {
		let pre = DispatchInfo { weight: Weight::from_parts(1000, 0), ..Default::default() };
		assert_eq!(extract_actual_pays_fee(&Ok(from_actual_ref_time(Some(7))), &pre), Pays::Yes);
		assert_eq!(
			extract_actual_pays_fee(&Ok(from_actual_ref_time(Some(1000)).into()), &pre),
			Pays::Yes
		);
		assert_eq!(
			extract_actual_pays_fee(&Ok(from_post_weight_info(Some(1000), Pays::Yes)), &pre),
			Pays::Yes
		);
		assert_eq!(
			extract_actual_pays_fee(&Ok(from_post_weight_info(Some(1000), Pays::No)), &pre),
			Pays::No
		);
		assert_eq!(
			extract_actual_pays_fee(
				&Err(DispatchError::BadOrigin.with_weight(Weight::from_parts(9, 0))),
				&pre
			),
			Pays::Yes
		);
		assert_eq!(
			extract_actual_pays_fee(
				&Err(DispatchErrorWithPostInfo {
					post_info: PostDispatchInfo { actual_weight: None, pays_fee: Pays::No },
					error: DispatchError::BadOrigin,
				}),
				&pre
			),
			Pays::No
		);

		let pre = DispatchInfo {
			weight: Weight::from_parts(1000, 0),
			pays_fee: Pays::No,
			..Default::default()
		};
		assert_eq!(extract_actual_pays_fee(&Ok(from_actual_ref_time(Some(7))), &pre), Pays::No);
		assert_eq!(extract_actual_pays_fee(&Ok(from_actual_ref_time(Some(1000))), &pre), Pays::No);
		assert_eq!(
			extract_actual_pays_fee(&Ok(from_post_weight_info(Some(1000), Pays::Yes)), &pre),
			Pays::No
		);
	}
}

#[cfg(test)]
mod per_dispatch_class_tests {
	use super::*;
	use sp_runtime::traits::Zero;
	use DispatchClass::*;

	#[test]
	fn add_works() {
		let a = PerDispatchClass {
			normal: (5, 10).into(),
			operational: (20, 30).into(),
			mandatory: Weight::MAX,
		};
		assert_eq!(
			a.clone()
				.add((20, 5).into(), Normal)
				.add((10, 10).into(), Operational)
				.add((u64::MAX, 3).into(), Mandatory),
			PerDispatchClass {
				normal: (25, 15).into(),
				operational: (30, 40).into(),
				mandatory: Weight::MAX
			}
		);
		let b = a
			.add(Weight::MAX, Normal)
			.add(Weight::MAX, Operational)
			.add(Weight::MAX, Mandatory);
		assert_eq!(
			b,
			PerDispatchClass {
				normal: Weight::MAX,
				operational: Weight::MAX,
				mandatory: Weight::MAX
			}
		);
		assert_eq!(b.total(), Weight::MAX);
	}

	#[test]
	fn accrue_works() {
		let mut a = PerDispatchClass::default();

		a.accrue((10, 15).into(), Normal);
		assert_eq!(a.normal, (10, 15).into());
		assert_eq!(a.total(), (10, 15).into());

		a.accrue((20, 25).into(), Operational);
		assert_eq!(a.operational, (20, 25).into());
		assert_eq!(a.total(), (30, 40).into());

		a.accrue((30, 35).into(), Mandatory);
		assert_eq!(a.mandatory, (30, 35).into());
		assert_eq!(a.total(), (60, 75).into());

		a.accrue((u64::MAX, 10).into(), Operational);
		assert_eq!(a.operational, (u64::MAX, 35).into());
		assert_eq!(a.total(), (u64::MAX, 85).into());

		a.accrue((10, u64::MAX).into(), Normal);
		assert_eq!(a.normal, (20, u64::MAX).into());
		assert_eq!(a.total(), Weight::MAX);
	}

	#[test]
	fn reduce_works() {
		let mut a = PerDispatchClass {
			normal: (10, u64::MAX).into(),
			mandatory: (u64::MAX, 10).into(),
			operational: (20, 20).into(),
		};

		a.reduce((5, 100).into(), Normal);
		assert_eq!(a.normal, (5, u64::MAX - 100).into());
		assert_eq!(a.total(), (u64::MAX, u64::MAX - 70).into());

		a.reduce((15, 5).into(), Operational);
		assert_eq!(a.operational, (5, 15).into());
		assert_eq!(a.total(), (u64::MAX, u64::MAX - 75).into());

		a.reduce((50, 0).into(), Mandatory);
		assert_eq!(a.mandatory, (u64::MAX - 50, 10).into());
		assert_eq!(a.total(), (u64::MAX - 40, u64::MAX - 75).into());

		a.reduce((u64::MAX, 100).into(), Operational);
		assert!(a.operational.is_zero());
		assert_eq!(a.total(), (u64::MAX - 45, u64::MAX - 90).into());

		a.reduce((5, u64::MAX).into(), Normal);
		assert!(a.normal.is_zero());
		assert_eq!(a.total(), (u64::MAX - 50, 10).into());
	}

	#[test]
	fn checked_accrue_works() {
		let mut a = PerDispatchClass::default();

		a.checked_accrue((1, 2).into(), Normal).unwrap();
		a.checked_accrue((3, 4).into(), Operational).unwrap();
		a.checked_accrue((5, 6).into(), Mandatory).unwrap();
		a.checked_accrue((7, 8).into(), Operational).unwrap();
		a.checked_accrue((9, 0).into(), Normal).unwrap();

		assert_eq!(
			a,
			PerDispatchClass {
				normal: (10, 2).into(),
				operational: (10, 12).into(),
				mandatory: (5, 6).into(),
			}
		);

		a.checked_accrue((u64::MAX - 10, u64::MAX - 2).into(), Normal).unwrap();
		a.checked_accrue((0, 0).into(), Normal).unwrap();
		a.checked_accrue((1, 0).into(), Normal).unwrap_err();
		a.checked_accrue((0, 1).into(), Normal).unwrap_err();

		assert_eq!(
			a,
			PerDispatchClass {
				normal: Weight::MAX,
				operational: (10, 12).into(),
				mandatory: (5, 6).into(),
			}
		);
	}

	#[test]
	fn checked_accrue_does_not_modify_on_error() {
		let mut a = PerDispatchClass {
			normal: 0.into(),
			operational: Weight::MAX / 2 + 2.into(),
			mandatory: 10.into(),
		};

		a.checked_accrue(Weight::MAX / 2, Operational).unwrap_err();
		a.checked_accrue(Weight::MAX - 9.into(), Mandatory).unwrap_err();
		a.checked_accrue(Weight::MAX, Normal).unwrap(); // This one works

		assert_eq!(
			a,
			PerDispatchClass {
				normal: Weight::MAX,
				operational: Weight::MAX / 2 + 2.into(),
				mandatory: 10.into(),
			}
		);
	}

	#[test]
	fn total_works() {
		assert!(PerDispatchClass::default().total().is_zero());

		assert_eq!(
			PerDispatchClass {
				normal: 0.into(),
				operational: (10, 20).into(),
				mandatory: (20, u64::MAX).into(),
			}
			.total(),
			(30, u64::MAX).into()
		);

		assert_eq!(
			PerDispatchClass {
				normal: (u64::MAX - 10, 10).into(),
				operational: (3, u64::MAX).into(),
				mandatory: (4, u64::MAX).into(),
			}
			.total(),
			(u64::MAX - 3, u64::MAX).into()
		);
	}
}
