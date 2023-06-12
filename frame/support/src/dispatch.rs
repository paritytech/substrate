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

impl<AccountId> RawOrigin<AccountId> {
	/// Returns `Some` with a reference to the `AccountId` if `self` is `Signed`, `None` otherwise.
	pub fn as_signed(&self) -> Option<&AccountId> {
		match &self {
			Self::Signed(x) => Some(x),
			_ => None,
		}
	}

	/// Returns `true` if `self` is `Root`, `None` otherwise.
	pub fn is_root(&self) -> bool {
		matches!(&self, Self::Root)
	}

	/// Returns `true` if `self` is `None`, `None` otherwise.
	pub fn is_none(&self) -> bool {
		matches!(&self, Self::None)
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

/// Declares a `Module` struct and a `Call` enum, which implements the dispatch logic.
///
/// ## Declaration
///
/// ```
/// # #[macro_use]
/// # extern crate frame_support;
/// # use frame_support::dispatch;
/// # use frame_system::{Config, ensure_signed};
/// decl_module! {
/// 	pub struct Module<T: Config> for enum Call where origin: T::RuntimeOrigin {
///
/// 		// Private functions are dispatchable, but not available to other
/// 		// FRAME pallets.
/// 		#[weight = 0]
/// 		fn my_function(origin, var: u64) -> dispatch::DispatchResult {
/// 				// Your implementation
/// 				Ok(())
/// 		}
///
/// 			// Public functions are both dispatchable and available to other
/// 		// FRAME pallets.
/// 		#[weight = 0]
/// 			pub fn my_public_function(origin) -> dispatch::DispatchResult {
/// 			// Your implementation
/// 				Ok(())
/// 		}
/// 		}
/// }
/// # fn main() {}
/// ```
///
/// The declaration is set with the header where:
///
/// * `Module`: The struct generated by the macro, with type `Config`.
/// * `Call`: The enum generated for every pallet, which implements
///   [`Callable`](./dispatch/trait.Callable.html).
/// * `origin`: Alias of `T::RuntimeOrigin`.
/// * `Result`: The expected return type from pallet functions.
///
/// The first parameter of dispatchable functions must always be `origin`.
///
/// ### Shorthand Example
///
/// The macro automatically expands a shorthand function declaration to return the
/// [`DispatchResult`] type. These functions are the same:
///
/// ```
/// # #[macro_use]
/// # extern crate frame_support;
/// # use frame_support::dispatch;
/// # use frame_system::{Config, ensure_signed};
/// decl_module! {
/// 	pub struct Module<T: Config> for enum Call where origin: T::RuntimeOrigin {
/// 		#[weight = 0]
/// 		fn my_long_function(origin) -> dispatch::DispatchResult {
/// 				// Your implementation
/// 			Ok(())
/// 		}
///
/// 		#[weight = 0]
/// 		fn my_short_function(origin) {
/// 				// Your implementation
/// 		}
/// 		}
/// }
/// # fn main() {}
/// ```
///
/// ### Consuming only portions of the annotated static weight
///
/// Per default a callable function consumes all of its static weight as declared via
/// the #\[weight\] attribute. However, there are use cases where only a portion of this
/// weight should be consumed. In that case the static weight is charged pre dispatch and
/// the difference is refunded post dispatch.
///
/// In order to make use of this feature the function must return `DispatchResultWithPostInfo`
/// in place of the default `DispatchResult`. Then the actually consumed weight can be returned.
/// To consume a non default weight while returning an error
/// [`WithPostDispatchInfo::with_weight`](./weight/trait.WithPostDispatchInfo.html) can be used
/// to augment any error with custom weight information.
///
/// ```
/// # #[macro_use]
/// # extern crate frame_support;
/// # use frame_support::{weights::Weight, dispatch::{DispatchResultWithPostInfo, WithPostDispatchInfo, PostDispatchInfo}};
/// # use frame_system::{Config, ensure_signed};
/// decl_module! {
/// 	pub struct Module<T: Config> for enum Call where origin: T::RuntimeOrigin {
/// 		#[weight = 1_000_000]
/// 		fn my_long_function(origin, do_expensive_calc: bool) -> DispatchResultWithPostInfo {
/// 			ensure_signed(origin).map_err(|e| e.with_weight(Weight::from_parts(100_000, 0)))?;
/// 			if do_expensive_calc {
/// 				// do the expensive calculation
/// 				// ...
/// 				// return None to indicate that we are using all weight (the default)
/// 				return Ok(None::<Weight>.into());
/// 			}
/// 			// expensive calculation not executed: use only a portion of the weight
/// 			Ok(PostDispatchInfo { actual_weight: Some(Weight::from_parts(100_000, 0)), ..Default::default() })
/// 		}
/// 	}
/// }
/// # fn main() {}
/// ```
///
/// ### Transactional Function Example
///
/// Transactional function discards all changes to storage if it returns `Err`, or commits if
/// `Ok`, via the #\[transactional\] attribute. Note the attribute must be after #\[weight\].
/// The #\[transactional\] attribute is deprecated since it is the default behaviour.
///
/// ```
/// # #[macro_use]
/// # extern crate frame_support;
/// # use frame_support::transactional;
/// # use frame_system::Config;
/// decl_module! {
/// 	pub struct Module<T: Config> for enum Call where origin: T::RuntimeOrigin {
/// 		#[weight = 0]
/// 		#[transactional]
/// 		fn my_short_function(origin) {
/// 				// Your implementation
/// 		}
/// 	}
/// }
/// # fn main() {}
/// ```
///
/// ### Privileged Function Example
///
/// A privileged function checks that the origin of the call is `ROOT`.
///
/// ```
/// # #[macro_use]
/// # extern crate frame_support;
/// # use frame_support::dispatch;
/// # use frame_system::{Config, ensure_signed, ensure_root};
/// decl_module! {
/// 	pub struct Module<T: Config> for enum Call where origin: T::RuntimeOrigin {
/// 		#[weight = 0]
/// 			fn my_privileged_function(origin) -> dispatch::DispatchResult {
/// 			ensure_root(origin)?;
/// 				// Your implementation
/// 			Ok(())
/// 		}
/// 		}
/// }
/// # fn main() {}
/// ```
///
/// ### Attributes on Functions
///
/// Attributes on functions are supported, but must be in the order of:
/// 1. Optional #\[doc\] attribute.
/// 2. #\[weight\] attribute.
/// 3. Optional function attributes, for instance #\[transactional\]. Those function attributes will
/// be written only on the dispatchable functions implemented on `Module`, not on the `Call` enum
/// variant.
///
/// ## Multiple Module Instances Example
///
/// A Substrate module can be built such that multiple instances of the same module can be used
/// within a single runtime. For example, the [Balances module](../pallet_balances/index.html) can
/// be added multiple times to your runtime in order to support multiple, independent currencies for
/// your blockchain. Here is an example of how you would declare such a module using the
/// `decl_module!` macro:
///
/// ```
/// # #[macro_use]
/// # extern crate frame_support;
/// # use frame_support::dispatch;
/// # use frame_system::ensure_signed;
/// # pub struct DefaultInstance;
/// # pub trait Instance: 'static {}
/// # impl Instance for DefaultInstance {}
/// pub trait Config<I: Instance=DefaultInstance>: frame_system::Config {}
///
/// decl_module! {
/// 	pub struct Module<T: Config<I>, I: Instance = DefaultInstance> for enum Call where origin: T::RuntimeOrigin {
/// 		// Your implementation
/// 	}
/// }
/// # fn main() {}
/// ```
///
/// Note: `decl_storage` must be called to generate `Instance` trait and optionally
/// `DefaultInstance` type.
///
/// ## Where clause
///
/// Besides the default `origin: T::RuntimeOrigin`, you can also pass other bounds to the module
/// declaration. This where bound will be replicated to all types generated by this macro. The
/// chaining of multiple trait bounds with `+` is not supported. If multiple bounds for one type are
/// required, it needs to be split up into multiple bounds.
///
/// ```
/// # #[macro_use]
/// # extern crate frame_support;
/// # use frame_support::dispatch;
/// # use frame_system::{self as system, ensure_signed};
/// pub trait Config: system::Config where Self::AccountId: From<u32> {}
///
/// decl_module! {
/// 	pub struct Module<T: Config> for enum Call where origin: T::RuntimeOrigin, T::AccountId: From<u32> {
/// 		// Your implementation
/// 	}
/// }
/// # fn main() {}
/// ```
///
/// ## Reserved Functions
///
/// The following are reserved function signatures:
///
/// * `deposit_event`: Helper function for depositing an [event](https://docs.substrate.io/main-docs/build/events-errors/).
/// The default behavior is to call `deposit_event` from the [System
/// module](../frame_system/index.html). However, you can write your own implementation for events
/// in your runtime. To use the default behavior, add `fn deposit_event() = default;` to your
/// `Module`.
///
/// The following reserved functions also take the block number (with type `T::BlockNumber`) as an
/// optional input:
///
/// * `on_runtime_upgrade`: Executes at the beginning of a block prior to on_initialize when there
/// is a runtime upgrade. This allows each module to upgrade its storage before the storage items
/// are used. As such, **calling other modules must be avoided**!! Using this function will
/// implement the [`OnRuntimeUpgrade`](../sp_runtime/traits/trait.OnRuntimeUpgrade.html) trait.
/// Function signature must be `fn on_runtime_upgrade() -> frame_support::weights::Weight`.
///
/// * `on_initialize`: Executes at the beginning of a block. Using this function will
/// implement the [`OnInitialize`](./trait.OnInitialize.html) trait.
/// Function signature can be either:
///   * `fn on_initialize(n: BlockNumber) -> frame_support::weights::Weight` or
///   * `fn on_initialize() -> frame_support::weights::Weight`
///
/// * `on_idle`: Executes at the end of a block. Passes a remaining weight to provide a threshold
/// for when to execute non vital functions. Using this function will implement the
/// [`OnIdle`](./traits/trait.OnIdle.html) trait.
/// Function signature is:
///   * `fn on_idle(n: BlockNumber, remaining_weight: Weight) -> frame_support::weights::Weight`
///
/// * `on_finalize`: Executes at the end of a block. Using this function will
/// implement the [`OnFinalize`](./traits/trait.OnFinalize.html) trait.
/// Function signature can be either:
///   * `fn on_finalize(n: BlockNumber) -> frame_support::weights::Weight` or
///   * `fn on_finalize() -> frame_support::weights::Weight`
///
/// * `offchain_worker`: Executes at the beginning of a block and produces extrinsics for a future
///   block upon completion. Using this function will implement the
///   [`OffchainWorker`](./traits/trait.OffchainWorker.html) trait.
/// * `integrity_test`: Executes in a test generated by `construct_runtime`, note it doesn't execute
///   in an externalities-provided environment. Implement
///   [`IntegrityTest`](./trait.IntegrityTest.html) trait.
#[macro_export]
#[deprecated(note = "Will be removed soon; use the attribute `#[pallet]` macro instead.
	For more info, see: <https://github.com/paritytech/substrate/pull/13705>")]
macro_rules! decl_module {
	// Entry point #1.
	(
		$(#[$attr:meta])*
		pub struct $mod_type:ident<
			$trait_instance:ident: $trait_name:ident
			$( <I>, I: $instantiable:path $( = $module_default_instance:path )? )?
		>
		for enum $call_type:ident where origin: $origin_type:ty $(, $where_ty:ty: $where_bound:path )* $(,)? {
			$( $t:tt )*
		}
	) => {
		$crate::decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<
				$trait_instance: $trait_name $(<I>, I: $instantiable $(= $module_default_instance)?)?
			>
			for enum $call_type where origin: $origin_type, system = frame_system
			{ $( $where_ty: $where_bound ),* }
			{}
			{}
			{}
			{}
			{}
			{}
			{}
			{}
			{}
			{}
			[]
			$($t)*
		);
	};
	// Entry point #2.
	(
		$(#[$attr:meta])*
		pub struct $mod_type:ident<
			$trait_instance:ident: $trait_name:ident
			$( <I>, I: $instantiable:path $( = $module_default_instance:path )? )?
		>
		for enum $call_type:ident where
			origin: $origin_type:ty,
			system = $system:ident
			$(, $where_ty:ty: $where_bound:path )*
			$(,)?
		{
			$($t:tt)*
		}
	) => {
		$crate::decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<
				$trait_instance: $trait_name $(<I>, I: $instantiable $( = $module_default_instance )? )?
			>
			for enum $call_type where origin: $origin_type, system = $system
			{ $( $where_ty: $where_bound ),* }
			{}
			{}
			{}
			{}
			{}
			{}
			{}
			{}
			{}
			{}
			[]
			$($t)*
		);
	};

	// Normalization expansions. Fills the defaults.
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident$(<I>, I: $instantiable:path $(= $module_default_instance:path)?)?>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{}
		{ $( $on_initialize:tt )* }
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		$vis:vis fn deposit_event() = default;
		$($rest:tt)*
	) => {
		$crate::decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<$trait_instance: $trait_name$(<I>, I: $instantiable $(= $module_default_instance)?)?>
			for enum $call_type where origin: $origin_type, system = $system
			{ $( $other_where_bounds )* }
			{ $vis fn deposit_event() = default; }
			{ $( $on_initialize )* }
			{ $( $on_runtime_upgrade )* }
			{ $( $on_idle )* }
			{ $( $on_finalize )* }
			{ $( $offchain )* }
			{ $( $constants )* }
			{ $( $error_type )* }
			{ $( $integrity_test )* }
			{ $( $storage_version )* }
			[ $( $dispatchables )* ]
			$($rest)*
		);
	};
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident$(<I>, I: $instantiable:path $(= $module_default_instance:path)?)?>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{}
		{ $( $on_initialize:tt )* }
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		$vis:vis fn deposit_event
		$($rest:tt)*
	) => {
		compile_error!(
			"`deposit_event` function is reserved and must follow the syntax: `$vis:vis fn deposit_event() = default;`"
		);
	};
	// Compile error on `deposit_event` being added a second time.
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<
			$trait_instance:ident: $trait_name:ident$(<I>, I: $instantiable:path $(= $module_default_instance:path)?)?
		>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )+ }
		{ $( $on_initialize:tt )* }
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		$vis:vis fn deposit_event() = default;
		$($rest:tt)*
	) => {
		compile_error!("`deposit_event` can only be passed once as input.");
	};
	// Add on_finalize
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident$(<I>, I: $instantiable:path $(= $module_default_instance:path)?)?>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )* }
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{}
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		fn on_finalize( $( $param_name:ident : $param:ty ),* $(,)? ) { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		$crate::decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<$trait_instance: $trait_name$(<I>, I: $instantiable $(= $module_default_instance)?)?>
			for enum $call_type where origin: $origin_type, system = $system
			{ $( $other_where_bounds )* }
			{ $( $deposit_event )* }
			{ $( $on_initialize )* }
			{ $( $on_runtime_upgrade )* }
			{ $( $on_idle )* }
			{
				fn on_finalize( $( $param_name : $param ),* ) { $( $impl )* }
			}
			{ $( $offchain )* }
			{ $( $constants )* }
			{ $( $error_type )* }
			{ $( $integrity_test )* }
			{ $( $storage_version )* }
			[ $( $dispatchables )* ]
			$($rest)*
		);
	};
	// compile_error on_finalize, given weight removed syntax.
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident$(<I>, I: $instantiable:path $(= $module_default_instance:path)?)?>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )* }
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{}
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		#[weight = $weight:expr]
		fn on_finalize( $( $param_name:ident : $param:ty ),* $(,)? ) { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		compile_error!(
			"`on_finalize` can't be given weight attribute anymore, weight must be returned by \
			`on_initialize` or `on_runtime_upgrade` instead"
		);
	};
	// Compile error on `on_finalize` being added a second time.
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<
			$trait_instance:ident: $trait_name:ident$(<I>, I: $instantiable:path $(= $module_default_instance:path)?)?
		>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )* }
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )+ }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		#[weight = $weight:expr]
		fn on_finalize( $( $param_name:ident : $param:ty ),* $(,)? ) { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		compile_error!("`on_finalize` can only be passed once as input.");
	};

	// Add on_idle
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident$(<I>, I: $instantiable:path $(= $module_default_instance:path)?)?>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )* }
		{ $( $on_runtime_upgrade:tt )* }
		{}
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		fn on_idle($param_name1:ident : $param1:ty, $param_name2:ident: $param2:ty $(,)? ) -> $return:ty { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		$crate::decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<$trait_instance: $trait_name$(<I>, I: $instantiable $(= $module_default_instance)?)?>
			for enum $call_type where origin: $origin_type, system = $system
			{ $( $other_where_bounds )* }
			{ $( $deposit_event )* }
			{ $( $on_initialize )* }
			{ $( $on_runtime_upgrade )* }
			{
				fn on_idle( $param_name1: $param1, $param_name2: $param2 ) -> $return { $( $impl )* }
			}
			{ $( $on_finalize:tt )* }
			{ $( $offchain )* }
			{ $( $constants )* }
			{ $( $error_type )* }
			{ $( $integrity_test )* }
			{ $( $storage_version )* }
			[ $( $dispatchables )* ]
			$($rest)*
		);
	};
	// compile_error for invalid on_idle function signature in decl_module
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<
			$trait_instance:ident: $trait_name:ident$(<I>, I: $instantiable:path $(= $module_default_instance:path)?)?
		>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )* }
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		$(#[weight = $weight:expr])?
		fn on_idle
		$($rest:tt)*
	) => {
		compile_error!("`on_idle` method is reserved and syntax doesn't match expected syntax.");
	};

	// compile_error on_runtime_upgrade, without a given weight removed syntax.
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<
			$trait_instance:ident: $trait_name:ident$(<I>, I: $instantiable:path $(= $module_default_instance:path)?)?
		>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )* }
		{}
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		fn on_runtime_upgrade( $( $param_name:ident : $param:ty ),* $(,)? ) { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		compile_error!(
			"`on_runtime_upgrade` must return Weight, signature has changed."
		);
	};
	// compile_error on_runtime_upgrade, given weight removed syntax.
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<
			$trait_instance:ident: $trait_name:ident$(<I>, I: $instantiable:path $(= $module_default_instance:path)?)?
		>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )* }
		{}
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		#[weight = $weight:expr]
		fn on_runtime_upgrade( $( $param_name:ident : $param:ty ),* $(,)? ) { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		compile_error!(
			"`on_runtime_upgrade` can't be given weight attribute anymore, weight must be returned \
			by the function directly."
		);
	};
	// Add on_runtime_upgrade
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<
			$trait_instance:ident: $trait_name:ident$(<I>, I: $instantiable:path $(= $module_default_instance:path)?)?
		>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )* }
		{}
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		fn on_runtime_upgrade( $( $param_name:ident : $param:ty ),* $(,)? ) -> $return:ty { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		$crate::decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<$trait_instance: $trait_name$(<I>, I: $instantiable $(= $module_default_instance)?)?>
			for enum $call_type where origin: $origin_type, system = $system
			{ $( $other_where_bounds )* }
			{ $( $deposit_event )* }
			{ $( $on_initialize )* }
			{
				fn on_runtime_upgrade( $( $param_name : $param ),* ) -> $return { $( $impl )* }
			}
			{ $( $on_idle )* }
			{ $( $on_finalize )* }
			{ $( $offchain )* }
			{ $( $constants )* }
			{ $( $error_type )* }
			{ $( $integrity_test )* }
			{ $( $storage_version )* }
			[ $( $dispatchables )* ]
			$($rest)*
		);
	};
	// Compile error on `on_runtime_upgrade` being added a second time.
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<
			$trait_instance:ident: $trait_name:ident$(<I>, I: $instantiable:path $(= $module_default_instance:path)?)?
		>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )* }
		{ $( $on_runtime_upgrade:tt )+ }
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		fn on_runtime_upgrade( $( $param_name:ident : $param:ty ),* $(,)? ) -> $return:ty { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		compile_error!("`on_runtime_upgrade` can only be passed once as input.");
	};
	// Add integrity_test
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<
			$trait_instance:ident: $trait_name:ident$(<I>, I: $instantiable:path $(= $module_default_instance:path)?)?
		>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )* }
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{}
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		fn integrity_test() { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		$crate::decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<$trait_instance: $trait_name$(<I>, I: $instantiable $(= $module_default_instance)?)?>
			for enum $call_type where origin: $origin_type, system = $system
			{ $( $other_where_bounds )* }
			{ $( $deposit_event )* }
			{ $( $on_initialize )* }
			{ $( $on_runtime_upgrade )* }
			{ $( $on_idle )* }
			{ $( $on_finalize )* }
			{ $( $offchain )* }
			{ $( $constants )* }
			{ $( $error_type )* }
			{
				$(#[doc = $doc_attr])*
				fn integrity_test() { $( $impl)* }
			}
			{ $( $storage_version )* }
			[ $( $dispatchables )* ]
			$($rest)*
		);
	};
	// Compile error on `integrity_test` being added a second time.
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<
			$trait_instance:ident: $trait_name:ident$(<I>, I: $instantiable:path $(= $module_default_instance:path)?)?
		>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )* }
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )+ }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		fn integrity_test() { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		compile_error!("`integrity_test` can only be passed once as input.");
	};
	// compile_error on_initialize, without a given weight removed syntax.
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<
			$trait_instance:ident: $trait_name:ident$(<I>, I: $instantiable:path $(= $module_default_instance:path)?)?
		>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{}
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		fn on_initialize( $( $param_name:ident : $param:ty ),* $(,)? ) { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		compile_error!(
			"`on_initialize` must return Weight, signature has changed."
		);
	};
	// compile_error on_initialize, with given weight removed syntax.
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<
			$trait_instance:ident: $trait_name:ident$(<I>, I: $instantiable:path $(= $module_default_instance:path)?)?
		>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{}
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		#[weight = $weight:expr]
		fn on_initialize( $( $param_name:ident : $param:ty ),* $(,)? ) { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		compile_error!(
			"`on_initialize` can't be given weight attribute anymore, weight must be returned \
			by the function directly."
		);
	};
	// Add on_initialize
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<
			$trait_instance:ident: $trait_name:ident$(<I>, I: $instantiable:path $(= $module_default_instance:path)?)?
		>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{}
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		fn on_initialize( $( $param_name:ident : $param:ty ),* $(,)? ) -> $return:ty { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		$crate::decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<$trait_instance: $trait_name$(<I>, I: $instantiable $(= $module_default_instance)?)?>
			for enum $call_type where origin: $origin_type, system = $system
			{ $( $other_where_bounds )* }
			{ $( $deposit_event )* }
			{
				fn on_initialize( $( $param_name : $param ),* ) -> $return { $( $impl )* }
			}
			{ $( $on_runtime_upgrade )* }
			{ $( $on_idle )* }
			{ $( $on_finalize )* }
			{ $( $offchain )* }
			{ $( $constants )* }
			{ $( $error_type )* }
			{ $( $integrity_test )* }
			{ $( $storage_version )* }
			[ $( $dispatchables )* ]
			$($rest)*
		);
	};
	// Compile error on trying to add a second `on_initialize`.
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<
			$trait_instance:ident: $trait_name:ident$(<I>, I: $instantiable:path $(= $module_default_instance:path)?)?
		>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )+ }
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		fn on_initialize( $( $param_name:ident : $param:ty ),* $(,)? ) -> $return:ty { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		compile_error!("`on_initialize` can only be passed once as input.");
	};
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<
			$trait_instance:ident: $trait_name:ident
			$(<I>, I: $instantiable:path $(= $module_default_instance:path)?)?
		>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )* }
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		fn offchain_worker( $( $param_name:ident : $param:ty ),* $(,)? ) { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		$crate::decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<
				$trait_instance: $trait_name$(<I>, I: $instantiable $(= $module_default_instance)?)?
			>
			for enum $call_type where origin: $origin_type, system = $system
			{ $( $other_where_bounds )* }
			{ $( $deposit_event )* }
			{ $( $on_initialize )* }
			{ $( $on_runtime_upgrade )* }
			{ $( $on_idle )* }
			{ $( $on_finalize )* }
			{ fn offchain_worker( $( $param_name : $param ),* ) { $( $impl )* } }
			{ $( $constants )* }
			{ $( $error_type )* }
			{ $( $integrity_test )* }
			{ $( $storage_version )* }
			[ $( $dispatchables )* ]
			$($rest)*
		);
	};
	// Compile error on trying to add a second `offchain_worker`.
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<
			$trait_instance:ident: $trait_name:ident$(<I>, I: $instantiable:path $(= $module_default_instance:path)?)?
		>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )* }
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )+ }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		fn offchain_worker( $( $param_name:ident : $param:ty ),* $(,)? ) -> $return:ty { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		compile_error!("`offchain_worker` can only be passed once as input.");
	};
	// This puts a constant in the parsed constants list.
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<
			$trait_instance:ident: $trait_name:ident
			$(<I>, $instance:ident: $instantiable:path $(= $module_default_instance:path)?)?
		>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )* }
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$( #[doc = $doc_attr:tt] )*
		const $name:ident: $ty:ty = $value:expr;
		$( $rest:tt )*
	) => {
		$crate::decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<
				$trait_instance: $trait_name
				$( <I>, $instance: $instantiable $(= $module_default_instance)? )?
			>
			for enum $call_type where origin: $origin_type, system = $system
			{ $( $other_where_bounds )* }
			{ $( $deposit_event )* }
			{ $( $on_initialize )* }
			{ $( $on_runtime_upgrade )* }
			{ $( $on_idle )* }
			{ $( $on_finalize )* }
			{ $( $offchain )* }
			{
				$( $constants )*
				$( #[doc = $doc_attr ] )*
				$name: $ty = $value;
			}
			{ $( $error_type )* }
			{ $( $integrity_test )* }
			{ $( $storage_version )* }
			[ $( $dispatchables )* ]
			$($rest)*
		);
	};

	// Parse error type
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<
			$trait_instance:ident:
				$trait_name:ident$(<I>, $instance:ident: $instantiable:path $(= $module_default_instance:path)?)?
			>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )* }
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		type Error = $error_type:ty;
		$($rest:tt)*
	) => {
		$crate::decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<
				$trait_instance: $trait_name$(<I>, $instance: $instantiable $(= $module_default_instance)?)?
			>
			for enum $call_type where origin: $origin_type, system = $system
			{ $( $other_where_bounds )* }
			{ $( $deposit_event )* }
			{ $( $on_initialize )* }
			{ $( $on_runtime_upgrade )* }
			{ $( $on_idle )* }
			{ $( $on_finalize )* }
			{ $( $offchain )* }
			{ $( $constants )* }
			{ $error_type }
			{ $( $integrity_test )* }
			{ $( $storage_version )* }
			[ $( $dispatchables )* ]
			$($rest)*
		);
	};
	// Add default Error if none supplied
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<
			$trait_instance:ident:
				$trait_name:ident$(<I>, $instance:ident: $instantiable:path $(= $module_default_instance:path)?)?
			>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )* }
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $($t:tt)* ]
		$($rest:tt)*
	) => {
		$crate::decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<
				$trait_instance: $trait_name$(<I>, $instance: $instantiable $(= $module_default_instance)?)?
			>
			for enum $call_type where origin: $origin_type, system = $system
			{ $( $other_where_bounds )* }
			{ $( $deposit_event )* }
			{ $( $on_initialize )* }
			{ $( $on_runtime_upgrade )* }
			{ $( $on_idle )* }
			{ $( $on_finalize )* }
			{ $( $offchain )* }
			{ $( $constants )* }
			{ __NO_ERROR_DEFINED }
			{ $( $integrity_test )* }
			{ $( $storage_version )* }
			[ $($t)* ]
			$($rest)*
		);
	};

	// Parse storage version
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<
			$trait_instance:ident:
				$trait_name:ident$(<I>, $instance:ident: $instantiable:path $(= $module_default_instance:path)?)?
			>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )* }
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		type StorageVersion = $storage_version:path;
		$($rest:tt)*
	) => {
		$crate::decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<
				$trait_instance: $trait_name$(<I>, $instance: $instantiable $(= $module_default_instance)?)?
			>
			for enum $call_type where origin: $origin_type, system = $system
			{ $( $other_where_bounds )* }
			{ $( $deposit_event )* }
			{ $( $on_initialize )* }
			{ $( $on_runtime_upgrade )* }
			{ $( $on_idle )* }
			{ $( $on_finalize )* }
			{ $( $offchain )* }
			{ $( $constants )* }
			{ $( $error_type )* }
			{ $( $integrity_test)* }
			{ $storage_version }
			[ $( $dispatchables )* ]
			$($rest)*
		);
	};

	// This puts the function statement into the [], decreasing `$rest` and moving toward finishing the parse.
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<
			$trait_instance:ident: $trait_name:ident
			$(<I>, $instance:ident: $instantiable:path $(= $module_default_instance:path)?)?
			>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )* }
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		#[weight = $weight:expr]
		$(#[$fn_attr:meta])*
		$fn_vis:vis fn $fn_name:ident(
			$origin:ident $( , $(#[$codec_attr:ident])* $param_name:ident : $param:ty )* $(,)?
		) $( -> $result:ty )* { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		$crate::decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<
				$trait_instance: $trait_name$(<I>, $instance: $instantiable $(= $module_default_instance)?)?
			>
			for enum $call_type where origin: $origin_type, system = $system
			{ $( $other_where_bounds )* }
			{ $( $deposit_event )* }
			{ $( $on_initialize )* }
			{ $( $on_runtime_upgrade )* }
			{ $( $on_idle )* }
			{ $( $on_finalize )* }
			{ $( $offchain )* }
			{ $( $constants )* }
			{ $( $error_type )* }
			{ $( $integrity_test)* }
			{ $( $storage_version )* }
			[
				$( $dispatchables )*
				$(#[doc = $doc_attr])*
				#[weight = $weight]
				$(#[$fn_attr])*
				$fn_vis fn $fn_name(
					$origin $( , $(#[$codec_attr])* $param_name : $param )*
				) $( -> $result )* { $( $impl )* }
				{ $($instance: $instantiable)? }
			]
			$($rest)*
		);
	};
	// Add #[weight] if none is defined.
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<
			$trait_instance:ident:
				$trait_name:ident$(<I>, $instance:ident: $instantiable:path $(= $module_default_instance:path)?)?
			>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )* }
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		$(#[$fn_attr:meta])*
		$fn_vis:vis fn $fn_name:ident(
			$from:ident $( , $( #[$codec_attr:ident] )* $param_name:ident : $param:ty )* $(,)?
		) $( -> $result:ty )* { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		compile_error!(concat!(
			"Missing weight for ", stringify!($ident),
			". Every dispatchable must have a #[weight] attribute."
			)
		);
	};
	// Ignore any ident which is not `origin` with type `T::RuntimeOrigin`.
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident$(<I>, I: $instantiable:path $(= $module_default_instance:path)?)?>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )* }
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		$(#[weight = $weight:expr])?
		$(#[$fn_attr:meta])*
		$fn_vis:vis fn $fn_name:ident(
			$origin:ident : T::RuntimeOrigin $( , $( #[$codec_attr:ident] )* $param_name:ident : $param:ty )* $(,)?
		) $( -> $result:ty )* { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		compile_error!(
			"First parameter of dispatch should be marked `origin` only, with no type specified \
			(a bit like `self`)."
		);
	};
	// Ignore any ident which is `origin` but has a type, regardless of the type token itself.
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident$(<I>, I: $instantiable:path $(= $module_default_instance:path)?)?>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )* }
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		$(#[weight = $weight:expr])?
		$(#[$fn_attr:meta])*
		$fn_vis:vis fn $fn_name:ident(
			origin : $origin:ty $( , $( #[$codec_attr:ident] )* $param_name:ident : $param:ty )* $(,)?
		) $( -> $result:ty )* { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		compile_error!(
			"First parameter of dispatch should be marked `origin` only, with no type specified \
			(a bit like `self`)."
		);
	};
	// Ignore any function missing `origin` as the first parameter.
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path $(= $module_default_instance:path)?)?>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )* }
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
		$(#[doc = $doc_attr:tt])*
		$(#[weight = $weight:expr])?
		$(#[$fn_attr:meta])*
		$fn_vis:vis fn $fn_name:ident(
			$( $(#[$codec_attr:ident])* $param_name:ident : $param:ty ),* $(,)?
		) $( -> $result:ty )* { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		compile_error!(
			"Implicit conversion to privileged function has been removed. \
			First parameter of dispatch should be marked `origin`. \
			For root-matching dispatch, also add `ensure_root(origin)?`."
		);
	};
	// Last normalize step. Triggers `@imp` expansion which is the real expansion.
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident$(<I>, I: $instantiable:path $(= $module_default_instance:path)?)?>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )* }
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
		[ $( $dispatchables:tt )* ]
	) => {
		$crate::decl_module!(@imp
			$(#[$attr])*
			pub struct $mod_type<$trait_instance: $trait_name$(<I>, I: $instantiable $(= $module_default_instance)?)?>
			for enum $call_type where origin: $origin_type, system = $system {
				$( $dispatchables )*
			}
			{ $( $other_where_bounds )* }
			{ $( $deposit_event )* }
			{ $( $on_initialize )* }
			{ $( $on_runtime_upgrade )* }
			{ $( $on_idle )* }
			{ $( $on_finalize )* }
			{ $( $offchain )* }
			{ $( $constants )* }
			{ $( $error_type )* }
			{ $( $integrity_test )* }
			{ $( $storage_version )* }
		);
	};

	// Implementation of Call enum's .dispatch() method.
	// TODO: this probably should be a different macro?

	(@call
		$ignore:ident
		$mod_type:ident<$trait_instance:ident $(, $instance:ident)?> $fn_name:ident $origin:ident $system:ident [ $( $param_name:ident),* ]
	) => {
			// We execute all dispatchable in a new storage layer, allowing them
			// to return an error at any point, and undoing any storage changes.
			$crate::storage::with_storage_layer(|| {
				<$mod_type<$trait_instance $(, $instance)?>>::$fn_name( $origin $(, $param_name )* ).map(Into::into).map_err(Into::into)
			})
	};

	// no `deposit_event` function wanted
	(@impl_deposit_event
		$module:ident<$trait_instance:ident: $trait_name:ident$(<I>, I: $instantiable:path)?>;
		$system:ident;
		{ $( $other_where_bounds:tt )* }
	) => {};

	(@impl_deposit_event
		$module:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>;
		$system:ident;
		{ $( $other_where_bounds:tt )* }
		$vis:vis fn deposit_event$(<$event_trait_instance:ident $(, $event_instance:ident)?>)?() = default;
	) => {
		impl<$trait_instance: $trait_name$(<I>, $instance: $instantiable)?> $module<$trait_instance $(, $instance)?>
			where $( $other_where_bounds )*
		{
			/// Deposits an event using `frame_system::Pallet::deposit_event`.
			$vis fn deposit_event(
				event: impl Into<< $trait_instance as $trait_name $(<$instance>)? >::RuntimeEvent>
			) {
				<$system::Pallet<$trait_instance>>::deposit_event(event.into())
			}
		}
	};

	(@impl_on_initialize
		{ $system:ident }
		$module:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>;
		{ $( $other_where_bounds:tt )* }
		fn on_initialize() -> $return:ty { $( $impl:tt )* }
	) => {
		impl<$trait_instance: $system::Config + $trait_name$(<I>, $instance: $instantiable)?>
			$crate::traits::OnInitialize<<$trait_instance as $system::Config>::BlockNumber>
			for $module<$trait_instance$(, $instance)?> where $( $other_where_bounds )*
		{
			fn on_initialize(_block_number_not_used: <$trait_instance as $system::Config>::BlockNumber) -> $return {
				$crate::sp_tracing::enter_span!($crate::sp_tracing::trace_span!("on_initialize"));
				{ $( $impl )* }
			}
		}
	};

	(@impl_on_initialize
		{ $system:ident }
		$module:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>;
		{ $( $other_where_bounds:tt )* }
		fn on_initialize($param:ident : $param_ty:ty) -> $return:ty { $( $impl:tt )* }
	) => {
		impl<$trait_instance: $system::Config + $trait_name$(<I>, $instance: $instantiable)?>
			$crate::traits::OnInitialize<<$trait_instance as $system::Config>::BlockNumber>
			for $module<$trait_instance$(, $instance)?> where $( $other_where_bounds )*
		{
			fn on_initialize($param: $param_ty) -> $return {
				$crate::sp_tracing::enter_span!($crate::sp_tracing::trace_span!("on_initialize"));
				{ $( $impl )* }
			}
		}
	};

	(@impl_on_initialize
		{ $system:ident }
		$module:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>;
		{ $( $other_where_bounds:tt )* }
	) => {
		impl<$trait_instance: $system::Config + $trait_name$(<I>, $instance: $instantiable)?>
			$crate::traits::OnInitialize<<$trait_instance as $system::Config>::BlockNumber>
			for $module<$trait_instance$(, $instance)?> where $( $other_where_bounds )*
		{}
	};

	(@impl_try_state_default
		{ $system:ident }
		$module:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>;
		{ $( $other_where_bounds:tt )* }
	) => {
		#[cfg(feature = "try-runtime")]
		impl<$trait_instance: $system::Config + $trait_name$(<I>, $instance: $instantiable)?>
			$crate::traits::TryState<<$trait_instance as $system::Config>::BlockNumber>
			for $module<$trait_instance$(, $instance)?> where $( $other_where_bounds )*
		{
			fn try_state(
				_: <$trait_instance as $system::Config>::BlockNumber,
				_: $crate::traits::TryStateSelect,
			) -> Result<(), $crate::sp_runtime::TryRuntimeError> {
				let pallet_name = <<
					$trait_instance
					as
					$system::Config
				>::PalletInfo as $crate::traits::PalletInfo>::name::<Self>().unwrap_or("<unknown pallet name>");
				$crate::log::debug!(
					target: $crate::LOG_TARGET,
					"⚠️ pallet {} cannot have try-state because it is using decl_module!",
					pallet_name,
				);
				Ok(())
			}
		}
	};

	(@impl_on_runtime_upgrade
		{ $system:ident }
		$module:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>;
		{ $( $other_where_bounds:tt )* }
		fn on_runtime_upgrade() -> $return:ty { $( $impl:tt )* }
	) => {
		impl<$trait_instance: $trait_name$(<I>, $instance: $instantiable)?>
			$crate::traits::OnRuntimeUpgrade
			for $module<$trait_instance$(, $instance)?> where $( $other_where_bounds )*
		{
			fn on_runtime_upgrade() -> $return {
				$crate::sp_tracing::enter_span!($crate::sp_tracing::trace_span!("on_runtime_upgrade"));
				let pallet_name = <<
					$trait_instance
					as
					$system::Config
				>::PalletInfo as $crate::traits::PalletInfo>::name::<Self>().unwrap_or("<unknown pallet name>");

				$crate::log::info!(
					target: $crate::LOG_TARGET,
					"⚠️ {} declares internal migrations (which *might* execute). \
					 On-chain `{:?}` vs current storage version `{:?}`",
					pallet_name,
					<Self as $crate::traits::GetStorageVersion>::on_chain_storage_version(),
					<Self as $crate::traits::GetStorageVersion>::current_storage_version(),
				);

				{ $( $impl )* }
			}

			#[cfg(feature = "try-runtime")]
			fn pre_upgrade() -> Result<$crate::sp_std::vec::Vec<u8>, $crate::sp_runtime::TryRuntimeError> {
				Ok($crate::sp_std::vec::Vec::new())
			}

			#[cfg(feature = "try-runtime")]
			fn post_upgrade(_: $crate::sp_std::vec::Vec<u8>) -> Result<(), $crate::sp_runtime::TryRuntimeError> {
				Ok(())
			}
		}
	};

	(@impl_on_runtime_upgrade
		{ $system:ident }
		$module:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>;
		{ $( $other_where_bounds:tt )* }
	) => {
		impl<$trait_instance: $trait_name$(<I>, $instance: $instantiable)?>
			$crate::traits::OnRuntimeUpgrade
			for $module<$trait_instance$(, $instance)?> where $( $other_where_bounds )*
		{
			fn on_runtime_upgrade() -> $crate::dispatch::Weight {
				$crate::sp_tracing::enter_span!($crate::sp_tracing::trace_span!("on_runtime_upgrade"));
				let pallet_name = <<
					$trait_instance
					as
					$system::Config
				>::PalletInfo as $crate::traits::PalletInfo>::name::<Self>().unwrap_or("<unknown pallet name>");

				$crate::log::debug!(
					target: $crate::LOG_TARGET,
					"✅ no migration for {}",
					pallet_name,
				);

				$crate::dispatch::Weight::zero()
			}

			#[cfg(feature = "try-runtime")]
			fn pre_upgrade() -> Result<$crate::sp_std::vec::Vec<u8>, $crate::sp_runtime::TryRuntimeError> {
				Ok($crate::sp_std::vec::Vec::new())
			}

			#[cfg(feature = "try-runtime")]
			fn post_upgrade(_: $crate::sp_std::vec::Vec<u8>) -> Result<(), $crate::sp_runtime::TryRuntimeError> {
				Ok(())
			}
		}
	};

	(@impl_integrity_test
		$module:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>;
		{ $( $other_where_bounds:tt )* }
		$(#[doc = $doc_attr:tt])*
		fn integrity_test() { $( $impl:tt )* }
	) => {
		#[cfg(feature = "std")]
		impl<$trait_instance: $trait_name$(<I>, $instance: $instantiable)?>
			$crate::traits::IntegrityTest
			for $module<$trait_instance$(, $instance)?> where $( $other_where_bounds )*
		{
			$(#[doc = $doc_attr])*
			fn integrity_test() {
				$( $impl )*
			}
		}
	};

	(@impl_integrity_test
		$module:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>;
		{ $( $other_where_bounds:tt )* }
	) => {
		#[cfg(feature = "std")]
		impl<$trait_instance: $trait_name$(<I>, $instance: $instantiable)?>
			$crate::traits::IntegrityTest
			for $module<$trait_instance$(, $instance)?> where $( $other_where_bounds )*
		{}
	};

	(@impl_on_finalize
		{ $system:ident }
		$module:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>;
		{ $( $other_where_bounds:tt )* }
		fn on_finalize() { $( $impl:tt )* }
	) => {
		impl<$trait_instance: $system::Config + $trait_name$(<I>, $instance: $instantiable)?>
			$crate::traits::OnFinalize<<$trait_instance as $system::Config>::BlockNumber>
			for $module<$trait_instance$(, $instance)?> where $( $other_where_bounds )*
		{
			fn on_finalize(_block_number_not_used: <$trait_instance as $system::Config>::BlockNumber) {
				$crate::sp_tracing::enter_span!($crate::sp_tracing::trace_span!("on_finalize"));
				{ $( $impl )* }
			}
		}
	};

	(@impl_on_finalize
		{ $system:ident }
		$module:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>;
		{ $( $other_where_bounds:tt )* }
		fn on_finalize($param:ident : $param_ty:ty) { $( $impl:tt )* }
	) => {
		impl<$trait_instance: $system::Config + $trait_name$(<I>, $instance: $instantiable)?>
			$crate::traits::OnFinalize<<$trait_instance as $system::Config>::BlockNumber>
			for $module<$trait_instance$(, $instance)?> where $( $other_where_bounds )*
		{
			fn on_finalize($param: $param_ty) {
				$crate::sp_tracing::enter_span!($crate::sp_tracing::trace_span!("on_finalize"));
				{ $( $impl )* }
			}
		}
	};

	(@impl_on_finalize
		{ $system:ident }
		$module:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>;
		{ $( $other_where_bounds:tt )* }
	) => {
		impl<$trait_instance: $system::Config + $trait_name$(<I>, $instance: $instantiable)?>
			$crate::traits::OnFinalize<<$trait_instance as $system::Config>::BlockNumber>
			for $module<$trait_instance$(, $instance)?> where $( $other_where_bounds )*
		{
		}
	};

	(@impl_on_idle
		{ $system:ident }
		$module:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>;
		{ $( $other_where_bounds:tt )* }
		fn on_idle($param1:ident : $param1_ty:ty, $param2:ident: $param2_ty:ty) -> $return:ty { $( $impl:tt )* }
	) => {
		impl<$trait_instance: $system::Config + $trait_name$(<I>, $instance: $instantiable)?>
			$crate::traits::OnIdle<<$trait_instance as $system::Config>::BlockNumber>
			for $module<$trait_instance$(, $instance)?> where $( $other_where_bounds )*
		{
			fn on_idle($param1: $param1_ty, $param2: $param2_ty) -> $return {
				$crate::sp_tracing::enter_span!($crate::sp_tracing::trace_span!("on_idle"));
				{ $( $impl )* }
			}
		}
	};

	(@impl_on_idle
		{ $system:ident }
		$module:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>;
		{ $( $other_where_bounds:tt )* }
	) => {
		impl<$trait_instance: $system::Config + $trait_name$(<I>, $instance: $instantiable)?>
			$crate::traits::OnIdle<<$trait_instance as $system::Config>::BlockNumber>
			for $module<$trait_instance$(, $instance)?> where $( $other_where_bounds )*
		{
		}
	};

	(@impl_offchain
		{ $system:ident }
		$module:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>;
		{ $( $other_where_bounds:tt )* }
		fn offchain_worker() { $( $impl:tt )* }
	) => {
		impl<$trait_instance: $system::Config + $trait_name$(<I>, $instance: $instantiable)?>
			$crate::traits::OffchainWorker<<$trait_instance as $system::Config>::BlockNumber>
			for $module<$trait_instance$(, $instance)?> where $( $other_where_bounds )*
		{
			fn offchain_worker(_block_number_not_used: <$trait_instance as $system::Config>::BlockNumber) { $( $impl )* }
		}
	};

	(@impl_offchain
		{ $system:ident }
		$module:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>;
		{ $( $other_where_bounds:tt )* }
		fn offchain_worker($param:ident : $param_ty:ty) { $( $impl:tt )* }
	) => {
		impl<$trait_instance: $system::Config + $trait_name$(<I>, $instance: $instantiable)?>
			$crate::traits::OffchainWorker<<$trait_instance as $system::Config>::BlockNumber>
			for $module<$trait_instance$(, $instance)?> where $( $other_where_bounds )*
		{
			fn offchain_worker($param: $param_ty) { $( $impl )* }
		}
	};

	(@impl_offchain
		{ $system:ident }
		$module:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>;
		{ $( $other_where_bounds:tt )* }
	) => {
		impl<$trait_instance: $system::Config + $trait_name$(<I>, $instance: $instantiable)?>
			$crate::traits::OffchainWorker<<$trait_instance as $system::Config>::BlockNumber>
			for $module<$trait_instance$(, $instance)?> where $( $other_where_bounds )*
		{}
	};

	// Expansion for _origin_ dispatch functions with no return type.
	(@impl_function
		$module:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>;
		$origin_ty:ty;
		$ignore:ident;
		$(#[$fn_attr:meta])*
		$vis:vis fn $name:ident (
			$origin:ident $(, $param:ident : $param_ty:ty )*
		) { $( $impl:tt )* }
	) => {
		#[allow(unreachable_code)]
		$(#[$fn_attr])*
		$vis fn $name(
			$origin: $origin_ty $(, $param: $param_ty )*
		) -> $crate::dispatch::DispatchResult {
			$crate::storage::with_storage_layer(|| {
				$crate::sp_tracing::enter_span!($crate::sp_tracing::trace_span!(stringify!($name)));
				{ $( $impl )* }
				Ok(())
			})
		}
	};

	// Expansion for _origin_ dispatch functions with explicit return type.
	(@impl_function
		$module:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>;
		$origin_ty:ty;
		$ignore:ident;
		$(#[$fn_attr:meta])*
		$vis:vis fn $name:ident (
			$origin:ident $(, $param:ident : $param_ty:ty )*
		) -> $result:ty { $( $impl:tt )* }
	) => {
		$(#[$fn_attr])*
		$vis fn $name($origin: $origin_ty $(, $param: $param_ty )* ) -> $result {
			$crate::storage::with_storage_layer(|| {
				$crate::sp_tracing::enter_span!($crate::sp_tracing::trace_span!(stringify!($name)));
				$( $impl )*
			})
		}
	};

	// Declare a `Call` variant parameter that should be encoded `compact`.
	(@create_call_enum
		$call_type:ident;
		<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path $(= $module_default_instance:path)?)?>
		{ $( $other_where_bounds:tt )* }
		{ $( $generated_variants:tt )* }
		{ $( $current_params:tt )* }
		variant $fn_name:ident;
		$( #[doc = $doc_attr:tt] )*
		#[compact]
		$name:ident : $type:ty;
		$( $rest:tt )*
	) => {
		$crate::decl_module! {
			@create_call_enum
			$call_type;
			<$trait_instance: $trait_name $(<I>, $instance: $instantiable $(= $module_default_instance)? )?>
			{ $( $other_where_bounds )* }
			{ $( $generated_variants )* }
			{
				$( $current_params )*
				#[codec(compact)]
				$name: $type,
			}
			variant $fn_name;
			$( #[doc = $doc_attr] )*
			$( $rest )*
		}
	};

	// Declare a `Call` variant parameter.
	(@create_call_enum
		$call_type:ident;
		<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path $(= $module_default_instance:path)?)?>
		{ $( $other_where_bounds:tt )* }
		{ $( $generated_variants:tt )* }
		{ $( $current_params:tt )* }
		variant $fn_name:ident;
		$(#[doc = $doc_attr:tt])*
		$name:ident : $type:ty;
		$( $rest:tt )*
	) => {
		$crate::decl_module! {
			@create_call_enum
			$call_type;
			<$trait_instance: $trait_name $(<I>, $instance: $instantiable $(= $module_default_instance)? )?>
			{ $( $other_where_bounds )* }
			{ $( $generated_variants )* }
			{
				$( $current_params )*
				$name: $type,
			}
			variant $fn_name;
			$( #[doc = $doc_attr] )*
			$( $rest )*
		}
	};

	(@create_call_enum
		$call_type:ident;
		<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path $(= $module_default_instance:path)?)?>
		{ $( $other_where_bounds:tt )* }
		{ $( $generated_variants:tt )* }
		{ $( $current_params:tt )* }
		variant $fn_name:ident;
		$(#[doc = $doc_attr:tt])*
		$(
			variant $next_fn_name:ident;
			$( $rest:tt )*
		)?
	) => {
		$crate::decl_module! {
			@create_call_enum
			$call_type;
			<$trait_instance: $trait_name $(<I>, $instance: $instantiable $(= $module_default_instance)? )?>
			{ $( $other_where_bounds )* }
			{
				$( $generated_variants )*
				#[allow(non_camel_case_types)]
				$(#[doc = $doc_attr])*
				$fn_name {
					$( $current_params )*
				},
			}
			{}
			$(
				variant $next_fn_name;
				$( $rest )*
			)?
		}
	};

	(@create_call_enum
		$call_type:ident;
		<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path $(= $module_default_instance:path)?)?>
		{ $( $other_where_bounds:tt )* }
		{ $( $generated_variants:tt )* }
		{}
	) => {
		/// Dispatchable calls.
		///
		/// Each variant of this enum maps to a dispatchable function from the associated module.
		#[derive($crate::codec::Encode, $crate::codec::Decode, $crate::scale_info::TypeInfo)]
		#[scale_info(skip_type_params($trait_instance $(, $instance)?), capture_docs = "always")]
		pub enum $call_type<$trait_instance: $trait_name$(<I>, $instance: $instantiable $( = $module_default_instance)?)?>
			where $( $other_where_bounds )*
		{
			#[doc(hidden)]
			#[codec(skip)]
			__PhantomItem($crate::sp_std::marker::PhantomData<($trait_instance, $($instance)?)>, $crate::Never),
			$( $generated_variants )*
		}
	};

	// Implementation for `GetStorageVersion`.
	(@impl_get_storage_version
		$module:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>;
		{ $( $other_where_bounds:tt )* }
		$( $storage_version:tt )+
	) => {
		// Implement `GetStorageVersion` for `Pallet`
		impl<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?> $crate::traits::GetStorageVersion
			for $module<$trait_instance $(, $instance)?> where $( $other_where_bounds )*
		{
			type CurrentStorageVersion = $crate::traits::StorageVersion;

			fn current_storage_version() -> Self::CurrentStorageVersion {
				$( $storage_version )*
			}

			fn on_chain_storage_version() -> $crate::traits::StorageVersion {
				$crate::traits::StorageVersion::get::<Self>()
			}
		}

		// Implement `OnGenesis` for `Module`
		impl<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?> $crate::traits::OnGenesis
			for $module<$trait_instance $(, $instance)?> where $( $other_where_bounds )*
		{
			fn on_genesis() {
				let storage_version = <Self as $crate::traits::GetStorageVersion>::current_storage_version();
				storage_version.put::<Self>();
			}
		}
	};

	// Implementation for `GetStorageVersion` when no storage version is passed.
	(@impl_get_storage_version
		$module:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>;
		{ $( $other_where_bounds:tt )* }
	) => {
		// Implement `GetStorageVersion` for `Pallet`
		impl<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?> $crate::traits::GetStorageVersion
			for $module<$trait_instance $(, $instance)?> where $( $other_where_bounds )*
		{
			type CurrentStorageVersion = $crate::traits::NoStorageVersionSet;

			fn current_storage_version() -> Self::CurrentStorageVersion {
				Default::default()
			}

			fn on_chain_storage_version() -> $crate::traits::StorageVersion {
				$crate::traits::StorageVersion::get::<Self>()
			}
		}

		// Implement `OnGenesis` for `Module`
		impl<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?> $crate::traits::OnGenesis
			for $module<$trait_instance $(, $instance)?> where $( $other_where_bounds )*
		{
			fn on_genesis() {
				let storage_version = $crate::traits::StorageVersion::default();
				storage_version.put::<Self>();
			}
		}
	};

	// The main macro expansion that actually renders the module code.

	(@imp
		$(#[$attr:meta])*
		pub struct $mod_type:ident<
			$trait_instance:ident: $trait_name:ident
			$(<I>, $instance:ident: $instantiable:path $(= $module_default_instance:path)?)?
		>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident {
			$(
				$(#[doc = $doc_attr:tt])*
				#[weight = $weight:expr]
				$(#[$fn_attr:meta])*
				$fn_vis:vis fn $fn_name:ident(
					$from:ident $( , $(#[$codec_attr:ident])* $param_name:ident : $param:ty)*
				) $( -> $result:ty )* { $( $impl:tt )* }
				{ $($fn_instance:ident: $fn_instantiable:path)? }
			)*
		}
		{ $( $other_where_bounds:tt )* }
		{ $( $deposit_event:tt )* }
		{ $( $on_initialize:tt )* }
		{ $( $on_runtime_upgrade:tt )* }
		{ $( $on_idle:tt )* }
		{ $( $on_finalize:tt )* }
		{ $( $offchain:tt )* }
		{ $( $constants:tt )* }
		{ $( $error_type:tt )* }
		{ $( $integrity_test:tt )* }
		{ $( $storage_version:tt )* }
	) => {
		$crate::__check_reserved_fn_name! { $( $fn_name )* }

		// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
		#[derive(Clone, Copy, PartialEq, Eq, $crate::RuntimeDebug)]
		$( #[$attr] )*
		pub struct $mod_type<
			$trait_instance: $trait_name
			$(<I>, $instance: $instantiable $( = $module_default_instance)?)?
		>($crate::sp_std::marker::PhantomData<($trait_instance, $( $instance)?)>) where
			$( $other_where_bounds )*;

		/// Type alias to `Module`, to be used by `construct_runtime`.
		#[allow(dead_code)]
		pub type Pallet<$trait_instance $(, $instance $( = $module_default_instance)?)?>
			= $mod_type<$trait_instance $(, $instance)?>;

		$crate::__create_tt_macro! {
			tt_error_token,
		}

		$crate::decl_module! {
			@impl_on_initialize
			{ $system }
			$mod_type<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?>;
			{ $( $other_where_bounds )* }
			$( $on_initialize )*
		}

		$crate::decl_module! {
			@impl_try_state_default
			{ $system }
			$mod_type<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?>;
			{ $( $other_where_bounds )* }
		}

		$crate::decl_module! {
			@impl_on_runtime_upgrade
			{ $system }
			$mod_type<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?>;
			{ $( $other_where_bounds )* }
			$( $on_runtime_upgrade )*
		}

		$crate::decl_module! {
			@impl_on_finalize
			{ $system }
			$mod_type<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?>;
			{ $( $other_where_bounds )* }
			$( $on_finalize )*
		}

		$crate::decl_module! {
			@impl_on_idle
			{ $system }
			$mod_type<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?>;
			{ $( $other_where_bounds )* }
			$( $on_idle )*
		}

		$crate::decl_module! {
			@impl_offchain
			{ $system }
			$mod_type<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?>;
			{ $( $other_where_bounds )* }
			$( $offchain )*
		}

		$crate::decl_module! {
			@impl_deposit_event
			$mod_type<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?>;
			$system;
			{ $( $other_where_bounds )* }
			$( $deposit_event )*
		}

		$crate::decl_module! {
			@impl_integrity_test
			$mod_type<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?>;
			{ $( $other_where_bounds )* }
			$( $integrity_test )*
		}

		/// Can also be called using [`Call`].
		///
		/// [`Call`]: enum.Call.html
		impl<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?> $mod_type<$trait_instance $(, $instance)?>
			where $( $other_where_bounds )*
		{
			$(
				$crate::decl_module! {
					@impl_function
					$mod_type<$trait_instance: $trait_name $(<I>, $fn_instance: $fn_instantiable)?>;
					$origin_type;
					$from;
					$(#[doc = $doc_attr])*
					///
					/// NOTE: Calling this function will bypass origin filters.
					$(#[$fn_attr])*
					$fn_vis fn $fn_name (
						$from $(, $param_name : $param )*
					) $( -> $result )* { $( $impl )* }
				}
			)*
		}

		$crate::decl_module! {
			@create_call_enum
			$call_type;
			<$trait_instance: $trait_name $(<I>, $instance: $instantiable $(= $module_default_instance)? )?>
			{ $( $other_where_bounds )* }
			{}
			{}
			$(
				variant $fn_name;
				$(#[doc = $doc_attr])*
				$(
					$(#[$codec_attr])*
					$param_name : $param;
				)*
			)*
		}

		$crate::paste::paste! {
			impl<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?>
				$call_type<$trait_instance $(, $instance)?> where $( $other_where_bounds )*
			{
				$(
					#[doc = "Create a call with the variant `" $fn_name "`."]
					pub fn [< new_call_variant_ $fn_name >](
						$( $param_name: $param ),*
					) -> Self {
						Self::$fn_name {
							$( $param_name ),*
						}
					}
				)*
			}
		}

		$crate::decl_module! {
			@impl_get_storage_version
			$mod_type<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?>;
			{ $( $other_where_bounds )* }
			$( $storage_version )*
		}

		// Implement weight calculation function for Call
		impl<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?> $crate::dispatch::GetDispatchInfo
			for $call_type<$trait_instance $(, $instance)?> where $( $other_where_bounds )*
		{
			fn get_dispatch_info(&self) -> $crate::dispatch::DispatchInfo {
				match *self {
					$(
						$call_type::$fn_name { $( ref $param_name ),* } => {
							let __pallet_base_weight = $weight;
							let __pallet_weight = <dyn $crate::dispatch::WeighData<( $( & $param, )* )>>::weigh_data(
								&__pallet_base_weight,
								($( $param_name, )*)
							);
							let __pallet_class = <dyn $crate::dispatch::ClassifyDispatch<( $( & $param, )* )>>::classify_dispatch(
								&__pallet_base_weight,
								($( $param_name, )*)
							);
							let __pallet_pays_fee = <dyn $crate::dispatch::PaysFee<( $( & $param, )* )>>::pays_fee(
								&__pallet_base_weight,
								($( $param_name, )*)
							);
							$crate::dispatch::DispatchInfo {
								weight: __pallet_weight,
								class: __pallet_class,
								pays_fee: __pallet_pays_fee,
							}
						},
					)*
					$call_type::__PhantomItem(_, _) => unreachable!("__PhantomItem should never be used."),
				}
			}
		}

		// Implement PalletInfoAccess for the module.
		impl<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?> $crate::traits::PalletInfoAccess
			for $mod_type<$trait_instance $(, $instance)?> where $( $other_where_bounds )*
		{
			fn index() -> usize {
				<
					<$trait_instance as $system::Config>::PalletInfo as $crate::traits::PalletInfo
				>::index::<Self>()
					.expect("Pallet is part of the runtime because pallet `Config` trait is \
						implemented by the runtime")
			}

			fn name() -> &'static str {
				<
					<$trait_instance as $system::Config>::PalletInfo as $crate::traits::PalletInfo
				>::name::<Self>()
					.expect("Pallet is part of the runtime because pallet `Config` trait is \
						implemented by the runtime")
			}

			fn module_name() -> &'static str {
				<
					<$trait_instance as $system::Config>::PalletInfo as $crate::traits::PalletInfo
				>::module_name::<Self>()
					.expect("Pallet is part of the runtime because pallet `Config` trait is \
						implemented by the runtime")
			}

			fn crate_version() -> $crate::traits::CrateVersion {
				$crate::crate_to_crate_version!()
			}
		}

		impl<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?> $crate::traits::PalletsInfoAccess
			for $mod_type<$trait_instance $(, $instance)?> where $( $other_where_bounds )*
		{
			fn count() -> usize { 1 }
			fn infos() -> $crate::sp_std::vec::Vec<$crate::traits::PalletInfoData> {
				use $crate::traits::PalletInfoAccess;
				let item = $crate::traits::PalletInfoData {
					index: Self::index(),
					name: Self::name(),
					module_name: Self::module_name(),
					crate_version: Self::crate_version(),
				};
				vec![item]
			}
		}

		// Implement GetCallName for the Call.
		impl<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?> $crate::dispatch::GetCallName
			for $call_type<$trait_instance $(, $instance)?> where $( $other_where_bounds )*
		{
			fn get_call_name(&self) -> &'static str {
				match *self {
					$(
						$call_type::$fn_name { $( ref $param_name ),* } => {
							// Don't generate any warnings for unused variables
							let _ = ( $( $param_name ),* );
							stringify!($fn_name)
						},
					)*
					$call_type::__PhantomItem(_, _) => unreachable!("__PhantomItem should never be used."),
				}
			}

			fn get_call_names() -> &'static [&'static str] {
				&[
					$(
						stringify!($fn_name),
					)*
				]
			}
		}

		// manual implementation of clone/eq/partialeq because using derive erroneously requires
		// clone/eq/partialeq from T.
		impl<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?> $crate::dispatch::Clone
			for $call_type<$trait_instance $(, $instance)?> where $( $other_where_bounds )*
		{
			fn clone(&self) -> Self {
				match *self {
					$(
						$call_type::$fn_name { $( ref $param_name ),* } =>
							$call_type::$fn_name { $( $param_name: (*$param_name).clone() ),* }
					,)*
					_ => unreachable!(),
				}
			}
		}

		impl<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?> $crate::dispatch::PartialEq
			for $call_type<$trait_instance $(, $instance)?> where $( $other_where_bounds )*
		{
			fn eq(&self, _other: &Self) -> bool {
				match *self {
					$(
						$call_type::$fn_name { $( ref $param_name ),* } => {
							let self_params = ( $( $param_name, )* );
							if let $call_type::$fn_name { $( ref $param_name ),* } = *_other {
								self_params == ( $( $param_name, )* )
							} else {
								match *_other {
									$call_type::__PhantomItem(_, _) => unreachable!(),
									_ => false,
								}
							}
						}
					)*
					_ => unreachable!(),
				}
			}
		}

		impl<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?> $crate::dispatch::Eq
			for $call_type<$trait_instance $(, $instance)?> where $( $other_where_bounds )*
		{}

		impl<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?> $crate::dispatch::fmt::Debug
			for $call_type<$trait_instance $(, $instance)?> where $( $other_where_bounds )*
		{
			fn fmt(
				&self,
				_f: &mut $crate::dispatch::fmt::Formatter,
			) -> $crate::dispatch::result::Result<(), $crate::dispatch::fmt::Error> {
				match *self {
					$(
						$call_type::$fn_name { $( ref $param_name ),* } =>
							write!(_f, "{}{:?}",
								stringify!($fn_name),
								( $( $param_name.clone(), )* )
							)
					,)*
					_ => unreachable!(),
				}
			}
		}

		impl<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?> $crate::traits::UnfilteredDispatchable
			for $call_type<$trait_instance $(, $instance)?> where $( $other_where_bounds )*
		{
			type RuntimeOrigin = $origin_type;
			fn dispatch_bypass_filter(self, _origin: Self::RuntimeOrigin) -> $crate::dispatch::DispatchResultWithPostInfo {
				match self {
					$(
						$call_type::$fn_name { $( $param_name ),* } => {
							$crate::decl_module!(
								@call
								$from
								$mod_type<$trait_instance $(, $fn_instance)?> $fn_name _origin $system [ $( $param_name ),* ]
							)
						},
					)*
					$call_type::__PhantomItem(_, _) => { unreachable!("__PhantomItem should never be used.") },
				}
			}
		}
		impl<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?> $crate::dispatch::Callable<$trait_instance>
			for $mod_type<$trait_instance $(, $instance)?> where $( $other_where_bounds )*
		{
			type RuntimeCall = $call_type<$trait_instance $(, $instance)?>;
		}

		$crate::__dispatch_impl_metadata! {
			$mod_type<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?>
			{ $( $other_where_bounds )* }
			$call_type $origin_type
			{
				$(
					$(#[doc = $doc_attr])*
					fn $fn_name($from $(, $(#[$codec_attr])* $param_name : $param )*);
				)*
			}
		}
		$crate::__impl_error_metadata! {
			$mod_type<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?>
			{ $( $other_where_bounds )* }
			$( $error_type )*
		}
		$crate::__impl_docs_metadata! {
			$mod_type<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?>
			{ $( $other_where_bounds )* }
		}
		$crate::__impl_module_constants_metadata ! {
			$mod_type<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?>
			{ $( $other_where_bounds )* }
			$( $constants )*
		}

		$crate::__generate_dummy_part_checker!();
	}
}

/// Implement metadata for dispatch.
#[macro_export]
#[doc(hidden)]
macro_rules! __dispatch_impl_metadata {
	(
		$mod_type:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>
		{ $( $other_where_bounds:tt )* }
		$call_type:ident
		$($rest:tt)*
	) => {
		impl<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?> $mod_type<$trait_instance $(, $instance)?>
			where $( $other_where_bounds )*
		{
			#[doc(hidden)]
			#[allow(dead_code)]
			pub fn call_functions() -> $crate::metadata_ir::PalletCallMetadataIR {
				$crate::scale_info::meta_type::<$call_type<$trait_instance $(, $instance)?>>().into()
			}
		}
	}
}

/// Implement metadata for pallet error.
#[macro_export]
#[doc(hidden)]
macro_rules! __impl_error_metadata {
	(
		$mod_type:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>
		{ $( $other_where_bounds:tt )* }
		__NO_ERROR_DEFINED
	) => {
		impl<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?> $mod_type<$trait_instance $(, $instance)?>
			where $( $other_where_bounds )*
		{
			#[doc(hidden)]
			#[allow(dead_code)]
			pub fn error_metadata() -> Option<$crate::metadata_ir::PalletErrorMetadataIR> {
				None
			}
		}
	};
	(
		$mod_type:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>
		{ $( $other_where_bounds:tt )* }
		$( $error_type:tt )*
	) => {
		impl<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?> $mod_type<$trait_instance $(, $instance)?>
			where $( $other_where_bounds )*
		{
			#[doc(hidden)]
			#[allow(dead_code)]
			pub fn error_metadata() -> Option<$crate::metadata_ir::PalletErrorMetadataIR> {
				Some($crate::metadata_ir::PalletErrorMetadataIR {
					ty: $crate::scale_info::meta_type::<$( $error_type )*>()
				})
			}
		}
	};
}

/// Implement metadata for pallet documentation.
#[macro_export]
#[doc(hidden)]
macro_rules! __impl_docs_metadata {
	(
		$mod_type:ident<$trait_instance:ident: $trait_name:ident$(<I>, $instance:ident: $instantiable:path)?>
		{ $( $other_where_bounds:tt )* }
	) => {
		impl<$trait_instance: $trait_name $(<I>, $instance: $instantiable)?> $mod_type<$trait_instance $(, $instance)?>
			where $( $other_where_bounds )*
		{
			#[doc(hidden)]
			#[allow(dead_code)]
			pub fn pallet_documentation_metadata() -> $crate::sp_std::vec::Vec<&'static str> {
				$crate::sp_std::vec![]
			}
		}
	};
}

/// Implement metadata for module constants.
#[macro_export]
#[doc(hidden)]
macro_rules! __impl_module_constants_metadata {
	// Without instance
	(
		$mod_type:ident<$trait_instance:ident: $trait_name:ident>
		{ $( $other_where_bounds:tt )* }
		$(
			$( #[doc = $doc_attr:tt] )*
			$name:ident: $type:ty = $value:expr;
		)*
	) => {
		$crate::paste::item! {
			$crate::__impl_module_constants_metadata! {
				GENERATE_CODE
				$mod_type<$trait_instance: $trait_name>
				{ $( $other_where_bounds )* }
				$(
					$( #[doc = $doc_attr] )*
					[< $name DefaultByteGetter >]
					$name<$trait_instance: $trait_name>: $type = $value;
				)*
			}
		}
	};
	// With instance
	(
		$mod_type:ident<$trait_instance:ident: $trait_name:ident<I>, $instance:ident: $instantiable:path>
		{ $( $other_where_bounds:tt )* }
		$(
			$( #[doc = $doc_attr:tt] )*
			$name:ident: $type:ty = $value:expr;
		)*
	) => {
		$crate::paste::item! {
			$crate::__impl_module_constants_metadata! {
				GENERATE_CODE
				$mod_type<$trait_instance: $trait_name<I>, $instance: $instantiable>
				{ $( $other_where_bounds )* }
				$(
					$( #[doc = $doc_attr] )*
					[< $name DefaultByteGetter >]
					$name<$trait_instance: $trait_name<I>, $instance: $instantiable>: $type = $value;
				)*
			}
		}
	};
	// Do the code generation
	(GENERATE_CODE
		$mod_type:ident<$trait_instance:ident: $trait_name:ident $(<I>, $instance:ident: $instantiable:path)?>
		{ $( $other_where_bounds:tt )* }
		$(
			$( #[doc = $doc_attr:tt] )*
			$default_byte_name:ident
			$name:ident<
				$const_trait_instance:ident: $const_trait_name:ident $(
					<I>, $const_instance:ident: $const_instantiable:path
				)*
			>: $type:ty = $value:expr;
		)*
	) => {
		impl<$trait_instance: 'static + $trait_name $(<I>, $instance: $instantiable)?>
			$mod_type<$trait_instance $(, $instance)?> where $( $other_where_bounds )*
		{
			#[doc(hidden)]
			#[allow(dead_code)]
			pub fn pallet_constants_metadata() -> $crate::sp_std::vec::Vec<$crate::metadata_ir::PalletConstantMetadataIR> {
				// Create the `ByteGetter`s
				$(
					#[allow(non_upper_case_types)]
					#[allow(non_camel_case_types)]
					struct $default_byte_name<
						$const_trait_instance: $const_trait_name $(
							<I>, $const_instance: $const_instantiable
						)?
					>($crate::dispatch::marker::PhantomData<
						($const_trait_instance, $( $const_instance)?)
					>);
					impl<$const_trait_instance: 'static + $const_trait_name $(
						<I>, $const_instance: $const_instantiable)?
					> $default_byte_name <$const_trait_instance $(, $const_instance)?>
					{
						fn default_byte(&self) -> $crate::dispatch::Vec<u8> {
							let value: $type = $value;
							$crate::dispatch::Encode::encode(&value)
						}
					}
				)*
				$crate::sp_std::vec![
					$(
						$crate::metadata_ir::PalletConstantMetadataIR {
							name: stringify!($name),
							ty: $crate::scale_info::meta_type::<$type>(),
							value: $default_byte_name::<$const_trait_instance $(, $const_instance)?>(
								Default::default()
							).default_byte(),
							docs: $crate::sp_std::vec![ $( $doc_attr ),* ],
						}
					),*
				]
			}
		}
	}
}

#[macro_export]
#[doc(hidden)]
macro_rules! __check_reserved_fn_name {
	(deposit_event $( $rest:ident )*) => {
		$crate::__check_reserved_fn_name!(@compile_error deposit_event);
	};
	(on_initialize $( $rest:ident )*) => {
		$crate::__check_reserved_fn_name!(@compile_error on_initialize);
	};
	(on_runtime_upgrade $( $rest:ident )*) => {
		$crate::__check_reserved_fn_name!(@compile_error on_runtime_upgrade);
	};
	(on_idle $( $rest:ident )*) => {
		$crate::__check_reserved_fn_name!(@compile_error on_idle);
	};
	(on_finalize $( $rest:ident )*) => {
		$crate::__check_reserved_fn_name!(@compile_error on_finalize);
	};
	(offchain_worker $( $rest:ident )*) => {
		$crate::__check_reserved_fn_name!(@compile_error offchain_worker);
	};
	(integrity_test $( $rest:ident )*) => {
		$crate::__check_reserved_fn_name!(@compile_error integrity_test);
	};
	($t:ident $( $rest:ident )*) => {
		$crate::__check_reserved_fn_name!($( $rest )*);
	};
	() => {};
	(@compile_error $ident:ident) => {
		compile_error!(
			concat!(
				"Invalid call fn name: `",
				stringify!($ident),
				"`, name is reserved and doesn't match expected signature, please refer to ",
				"`decl_module!` documentation to see the appropriate usage, or rename it to an ",
				"unreserved keyword."
			),
		);
	};
	(@compile_error_renamed $ident:ident $new_ident:ident) => {
		compile_error!(
			concat!(
				"`",
				stringify!($ident),
				"` was renamed to `",
				stringify!($new_ident),
				"`. Please rename your function accordingly.",
			),
		);
	};
}

#[cfg(test)]
// Do not complain about unused `dispatch` and `dispatch_aux`.
#[allow(dead_code)]
#[allow(deprecated)]
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
