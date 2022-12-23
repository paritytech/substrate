// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Primitives for the runtime modules.

use crate::{
	codec::{Codec, Decode, Encode, MaxEncodedLen},
	generic::Digest,
	scale_info::{MetaType, StaticTypeInfo, TypeInfo},
	transaction_validity::{
		TransactionSource, TransactionValidity, TransactionValidityError, UnknownTransaction,
		ValidTransaction,
	},
	DispatchResult,
};
use impl_trait_for_tuples::impl_for_tuples;
#[cfg(feature = "std")]
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use sp_application_crypto::AppKey;
pub use sp_arithmetic::traits::{
	AtLeast32Bit, AtLeast32BitUnsigned, Bounded, CheckedAdd, CheckedDiv, CheckedMul, CheckedShl,
	CheckedShr, CheckedSub, IntegerSquareRoot, One, SaturatedConversion, Saturating,
	UniqueSaturatedFrom, UniqueSaturatedInto, Zero,
};
use sp_core::{self, storage::StateVersion, Hasher, RuntimeDebug, TypeId};
#[doc(hidden)]
pub use sp_core::{
	parameter_types, ConstBool, ConstI128, ConstI16, ConstI32, ConstI64, ConstI8, ConstU128,
	ConstU16, ConstU32, ConstU64, ConstU8, Get, GetDefault, TryCollect, TypedGet,
};
#[doc(hidden)]
pub use sp_std::marker::PhantomData;
use sp_std::{self, fmt::Debug, prelude::*};
#[cfg(feature = "std")]
use std::fmt::Display;
#[cfg(feature = "std")]
use std::str::FromStr;

/// A lazy value.
pub trait Lazy<T: ?Sized> {
	/// Get a reference to the underlying value.
	///
	/// This will compute the value if the function is invoked for the first time.
	fn get(&mut self) -> &T;
}

impl<'a> Lazy<[u8]> for &'a [u8] {
	fn get(&mut self) -> &[u8] {
		self
	}
}

/// Some type that is able to be collapsed into an account ID. It is not possible to recreate the
/// original value from the account ID.
pub trait IdentifyAccount {
	/// The account ID that this can be transformed into.
	type AccountId;
	/// Transform into an account.
	fn into_account(self) -> Self::AccountId;
}

impl IdentifyAccount for sp_core::ed25519::Public {
	type AccountId = Self;
	fn into_account(self) -> Self {
		self
	}
}

impl IdentifyAccount for sp_core::sr25519::Public {
	type AccountId = Self;
	fn into_account(self) -> Self {
		self
	}
}

impl IdentifyAccount for sp_core::ecdsa::Public {
	type AccountId = Self;
	fn into_account(self) -> Self {
		self
	}
}

/// Means of signature verification.
pub trait Verify {
	/// Type of the signer.
	type Signer: IdentifyAccount;
	/// Verify a signature.
	///
	/// Return `true` if signature is valid for the value.
	fn verify<L: Lazy<[u8]>>(
		&self,
		msg: L,
		signer: &<Self::Signer as IdentifyAccount>::AccountId,
	) -> bool;
}

impl Verify for sp_core::ed25519::Signature {
	type Signer = sp_core::ed25519::Public;

	fn verify<L: Lazy<[u8]>>(&self, mut msg: L, signer: &sp_core::ed25519::Public) -> bool {
		sp_io::crypto::ed25519_verify(self, msg.get(), signer)
	}
}

impl Verify for sp_core::sr25519::Signature {
	type Signer = sp_core::sr25519::Public;

	fn verify<L: Lazy<[u8]>>(&self, mut msg: L, signer: &sp_core::sr25519::Public) -> bool {
		sp_io::crypto::sr25519_verify(self, msg.get(), signer)
	}
}

impl Verify for sp_core::ecdsa::Signature {
	type Signer = sp_core::ecdsa::Public;
	fn verify<L: Lazy<[u8]>>(&self, mut msg: L, signer: &sp_core::ecdsa::Public) -> bool {
		match sp_io::crypto::secp256k1_ecdsa_recover_compressed(
			self.as_ref(),
			&sp_io::hashing::blake2_256(msg.get()),
		) {
			Ok(pubkey) => signer.as_ref() == &pubkey[..],
			_ => false,
		}
	}
}

/// Means of signature verification of an application key.
pub trait AppVerify {
	/// Type of the signer.
	type AccountId;
	/// Verify a signature. Return `true` if signature is valid for the value.
	fn verify<L: Lazy<[u8]>>(&self, msg: L, signer: &Self::AccountId) -> bool;
}

impl<
		S: Verify<Signer = <<T as AppKey>::Public as sp_application_crypto::AppPublic>::Generic>
			+ From<T>,
		T: sp_application_crypto::Wraps<Inner = S>
			+ sp_application_crypto::AppKey
			+ sp_application_crypto::AppSignature
			+ AsRef<S>
			+ AsMut<S>
			+ From<S>,
	> AppVerify for T
where
	<S as Verify>::Signer: IdentifyAccount<AccountId = <S as Verify>::Signer>,
	<<T as AppKey>::Public as sp_application_crypto::AppPublic>::Generic: IdentifyAccount<
		AccountId = <<T as AppKey>::Public as sp_application_crypto::AppPublic>::Generic,
	>,
{
	type AccountId = <T as AppKey>::Public;
	fn verify<L: Lazy<[u8]>>(&self, msg: L, signer: &<T as AppKey>::Public) -> bool {
		use sp_application_crypto::IsWrappedBy;
		let inner: &S = self.as_ref();
		let inner_pubkey =
			<<T as AppKey>::Public as sp_application_crypto::AppPublic>::Generic::from_ref(signer);
		Verify::verify(inner, msg, inner_pubkey)
	}
}

/// An error type that indicates that the origin is invalid.
#[derive(Encode, Decode, RuntimeDebug)]
pub struct BadOrigin;

impl From<BadOrigin> for &'static str {
	fn from(_: BadOrigin) -> &'static str {
		"Bad origin"
	}
}

/// An error that indicates that a lookup failed.
#[derive(Encode, Decode, RuntimeDebug)]
pub struct LookupError;

impl From<LookupError> for &'static str {
	fn from(_: LookupError) -> &'static str {
		"Can not lookup"
	}
}

impl From<LookupError> for TransactionValidityError {
	fn from(_: LookupError) -> Self {
		UnknownTransaction::CannotLookup.into()
	}
}

/// Means of changing one type into another in a manner dependent on the source type.
pub trait Lookup {
	/// Type to lookup from.
	type Source;
	/// Type to lookup into.
	type Target;
	/// Attempt a lookup.
	fn lookup(&self, s: Self::Source) -> Result<Self::Target, LookupError>;
}

/// Means of changing one type into another in a manner dependent on the source type.
/// This variant is different to `Lookup` in that it doesn't (can cannot) require any
/// context.
pub trait StaticLookup {
	/// Type to lookup from.
	type Source: Codec + Clone + PartialEq + Debug + TypeInfo;
	/// Type to lookup into.
	type Target;
	/// Attempt a lookup.
	fn lookup(s: Self::Source) -> Result<Self::Target, LookupError>;
	/// Convert from Target back to Source.
	fn unlookup(t: Self::Target) -> Self::Source;
}

/// A lookup implementation returning the input value.
#[derive(Default)]
pub struct IdentityLookup<T>(PhantomData<T>);
impl<T: Codec + Clone + PartialEq + Debug + TypeInfo> StaticLookup for IdentityLookup<T> {
	type Source = T;
	type Target = T;
	fn lookup(x: T) -> Result<T, LookupError> {
		Ok(x)
	}
	fn unlookup(x: T) -> T {
		x
	}
}

impl<T> Lookup for IdentityLookup<T> {
	type Source = T;
	type Target = T;
	fn lookup(&self, x: T) -> Result<T, LookupError> {
		Ok(x)
	}
}

/// A lookup implementation returning the `AccountId` from a `MultiAddress`.
pub struct AccountIdLookup<AccountId, AccountIndex>(PhantomData<(AccountId, AccountIndex)>);
impl<AccountId, AccountIndex> StaticLookup for AccountIdLookup<AccountId, AccountIndex>
where
	AccountId: Codec + Clone + PartialEq + Debug,
	AccountIndex: Codec + Clone + PartialEq + Debug,
	crate::MultiAddress<AccountId, AccountIndex>: Codec + StaticTypeInfo,
{
	type Source = crate::MultiAddress<AccountId, AccountIndex>;
	type Target = AccountId;
	fn lookup(x: Self::Source) -> Result<Self::Target, LookupError> {
		match x {
			crate::MultiAddress::Id(i) => Ok(i),
			_ => Err(LookupError),
		}
	}
	fn unlookup(x: Self::Target) -> Self::Source {
		crate::MultiAddress::Id(x)
	}
}

/// Perform a StaticLookup where there are multiple lookup sources of the same type.
impl<A, B> StaticLookup for (A, B)
where
	A: StaticLookup,
	B: StaticLookup<Source = A::Source, Target = A::Target>,
{
	type Source = A::Source;
	type Target = A::Target;

	fn lookup(x: Self::Source) -> Result<Self::Target, LookupError> {
		A::lookup(x.clone()).or_else(|_| B::lookup(x))
	}
	fn unlookup(x: Self::Target) -> Self::Source {
		A::unlookup(x)
	}
}

/// Extensible conversion trait. Generic over only source type, with destination type being
/// associated.
pub trait Morph<A> {
	/// The type into which `A` is mutated.
	type Outcome;

	/// Make conversion.
	fn morph(a: A) -> Self::Outcome;
}

/// A structure that performs identity conversion.
impl<T> Morph<T> for Identity {
	type Outcome = T;
	fn morph(a: T) -> T {
		a
	}
}

/// Extensible conversion trait. Generic over only source type, with destination type being
/// associated.
pub trait TryMorph<A> {
	/// The type into which `A` is mutated.
	type Outcome;

	/// Make conversion.
	fn try_morph(a: A) -> Result<Self::Outcome, ()>;
}

/// A structure that performs identity conversion.
impl<T> TryMorph<T> for Identity {
	type Outcome = T;
	fn try_morph(a: T) -> Result<T, ()> {
		Ok(a)
	}
}

/// Create a `Morph` and/or `TryMorph` impls with a simple closure-like expression.
///
/// # Examples
///
/// ```
/// # use sp_runtime::{morph_types, traits::{Morph, TryMorph, TypedGet, ConstU32}};
/// # use sp_arithmetic::traits::CheckedSub;
///
/// morph_types! {
///    /// Replace by some other value; produce both `Morph` and `TryMorph` implementations
///    pub type Replace<V: TypedGet> = |_| -> V::Type { V::get() };
///    /// A private `Morph` implementation to reduce a `u32` by 10.
///    type ReduceU32ByTen: Morph = |r: u32| -> u32 { r - 10 };
///    /// A `TryMorph` implementation to reduce a scalar by a particular amount, checking for
///    /// underflow.
///    pub type CheckedReduceBy<N: TypedGet>: TryMorph = |r: N::Type| -> Result<N::Type, ()> {
///        r.checked_sub(&N::get()).ok_or(())
///    } where N::Type: CheckedSub;
/// }
///
/// trait Config {
///    type TestMorph1: Morph<u32>;
///    type TestTryMorph1: TryMorph<u32>;
///    type TestMorph2: Morph<u32>;
///    type TestTryMorph2: TryMorph<u32>;
/// }
///
/// struct Runtime;
/// impl Config for Runtime {
///    type TestMorph1 = Replace<ConstU32<42>>;
///    type TestTryMorph1 = Replace<ConstU32<42>>;
///    type TestMorph2 = ReduceU32ByTen;
///    type TestTryMorph2 = CheckedReduceBy<ConstU32<10>>;
/// }
/// ```
#[macro_export]
macro_rules! morph_types {
	(
		@DECL $( #[doc = $doc:expr] )* $vq:vis $name:ident ()
	) => {
		$( #[doc = $doc] )* $vq struct $name;
	};
	(
		@DECL $( #[doc = $doc:expr] )* $vq:vis $name:ident ( $( $bound_id:ident ),+ )
	) => {
		$( #[doc = $doc] )*
		$vq struct $name < $($bound_id,)* > ( $crate::traits::PhantomData< ( $($bound_id,)* ) > ) ;
	};
	(
		@IMPL $name:ty : ( $( $bounds:tt )* ) ( $( $where:tt )* )
		= |$var:ident: $var_type:ty| -> $outcome:ty { $( $ex:expr )* }
	) => {
		impl<$($bounds)*> $crate::traits::Morph<$var_type> for $name $( $where )? {
			type Outcome = $outcome;
			fn morph($var: $var_type) -> Self::Outcome { $( $ex )* }
		}
	};
	(
		@IMPL_TRY $name:ty : ( $( $bounds:tt )* ) ( $( $where:tt )* )
		= |$var:ident: $var_type:ty| -> $outcome:ty { $( $ex:expr )* }
	) => {
		impl<$($bounds)*> $crate::traits::TryMorph<$var_type> for $name $( $where )? {
			type Outcome = $outcome;
			fn try_morph($var: $var_type) -> Result<Self::Outcome, ()> { $( $ex )* }
		}
	};
	(
		@IMPL $name:ty : () ( $( $where:tt )* )
		= |$var:ident: $var_type:ty| -> $outcome:ty { $( $ex:expr )* }
	) => {
		impl $crate::traits::Morph<$var_type> for $name $( $where )? {
			type Outcome = $outcome;
			fn morph($var: $var_type) -> Self::Outcome { $( $ex )* }
		}
	};
	(
		@IMPL_TRY $name:ty : () ( $( $where:tt )* )
		= |$var:ident: $var_type:ty| -> $outcome:ty { $( $ex:expr )* }
	) => {
		impl $crate::traits::TryMorph<$var_type> for $name $( $where )? {
			type Outcome = $outcome;
			fn try_morph($var: $var_type) -> Result<Self::Outcome, ()> { $( $ex )* }
		}
	};
	(
		@IMPL_BOTH $name:ty : ( $( $bounds:tt )* ) ( $( $where:tt )* )
		= |$var:ident: $var_type:ty| -> $outcome:ty { $( $ex:expr )* }
	) => {
		morph_types! {
			@IMPL $name : ($($bounds)*) ($($where)*)
			= |$var: $var_type| -> $outcome { $( $ex )* }
		}
		morph_types! {
			@IMPL_TRY $name : ($($bounds)*) ($($where)*)
			= |$var: $var_type| -> $outcome { Ok({$( $ex )*}) }
		}
	};

	(
		$( #[doc = $doc:expr] )* $vq:vis type $name:ident
		$( < $( $bound_id:ident $( : $bound_head:path $( | $bound_tail:path )* )? ),+ > )?
		$(: $type:tt)?
		= |_| -> $outcome:ty { $( $ex:expr )* };
		$( $rest:tt )*
	) => {
		morph_types! {
			$( #[doc = $doc] )* $vq type $name
			$( < $( $bound_id $( : $bound_head $( | $bound_tail )* )? ),+ > )?
			EXTRA_GENERIC(X)
			$(: $type)?
			= |_x: X| -> $outcome { $( $ex )* };
			$( $rest )*
		}
	};
	(
		$( #[doc = $doc:expr] )* $vq:vis type $name:ident
		$( < $( $bound_id:ident $( : $bound_head:path $( | $bound_tail:path )* )? ),+ > )?
		$( EXTRA_GENERIC ($extra:ident) )?
		= |$var:ident: $var_type:ty| -> $outcome:ty { $( $ex:expr )* }
		$( where $( $where_path:ty : $where_bound_head:path $( | $where_bound_tail:path )* ),* )?;
		$( $rest:tt )*
	) => {
		morph_types! { @DECL $( #[doc = $doc] )* $vq $name ( $( $( $bound_id ),+ )? ) }
		morph_types! {
			@IMPL_BOTH $name $( < $( $bound_id ),* > )? :
			( $( $( $bound_id $( : $bound_head $( + $bound_tail )* )? , )+ )? $( $extra )? )
			( $( where $( $where_path : $where_bound_head $( + $where_bound_tail )* ),* )? )
			= |$var: $var_type| -> $outcome { $( $ex )* }
		}
		morph_types!{ $($rest)* }
	};
	(
		$( #[doc = $doc:expr] )* $vq:vis type $name:ident
		$( < $( $bound_id:ident $( : $bound_head:path $( | $bound_tail:path )* )? ),+ > )?
		$( EXTRA_GENERIC ($extra:ident) )?
		: Morph
		= |$var:ident: $var_type:ty| -> $outcome:ty { $( $ex:expr )* }
		$( where $( $where_path:ty : $where_bound_head:path $( | $where_bound_tail:path )* ),* )?;
		$( $rest:tt )*
	) => {
		morph_types! { @DECL $( #[doc = $doc] )* $vq $name ( $( $( $bound_id ),+ )? ) }
		morph_types! {
			@IMPL $name $( < $( $bound_id ),* > )? :
			( $( $( $bound_id $( : $bound_head $( + $bound_tail )* )? , )+ )? $( $extra )? )
			( $( where $( $where_path : $where_bound_head $( + $where_bound_tail )* ),* )? )
			= |$var: $var_type| -> $outcome { $( $ex )* }
		}
		morph_types!{ $($rest)* }
	};
	(
		$( #[doc = $doc:expr] )* $vq:vis type $name:ident
		$( < $( $bound_id:ident $( : $bound_head:path $( | $bound_tail:path )* )? ),+ > )?
		$( EXTRA_GENERIC ($extra:ident) )?
		: TryMorph
		= |$var:ident: $var_type:ty| -> Result<$outcome:ty, ()> { $( $ex:expr )* }
		$( where $( $where_path:ty : $where_bound_head:path $( | $where_bound_tail:path )* ),* )?;
		$( $rest:tt )*
	) => {
		morph_types! { @DECL $( #[doc = $doc] )* $vq $name ( $( $( $bound_id ),+ )? ) }
		morph_types! {
			@IMPL_TRY $name $( < $( $bound_id ),* > )? :
			( $( $( $bound_id $( : $bound_head $( + $bound_tail )* )? , )+ )? $( $extra )? )
			( $( where $( $where_path : $where_bound_head $( + $where_bound_tail )* ),* )? )
			= |$var: $var_type| -> $outcome { $( $ex )* }
		}
		morph_types!{ $($rest)* }
	};
	() => {}
}

morph_types! {
	/// Morpher to disregard the source value and replace with another.
	pub type Replace<V: TypedGet> = |_| -> V::Type { V::get() };
	/// Mutator which reduces a scalar by a particular amount.
	pub type ReduceBy<N: TypedGet> = |r: N::Type| -> N::Type {
		r.checked_sub(&N::get()).unwrap_or(Zero::zero())
	} where N::Type: CheckedSub | Zero;
}

/// Extensible conversion trait. Generic over both source and destination types.
pub trait Convert<A, B> {
	/// Make conversion.
	fn convert(a: A) -> B;
}

impl<A, B: Default> Convert<A, B> for () {
	fn convert(_: A) -> B {
		Default::default()
	}
}

/// A structure that performs identity conversion.
pub struct Identity;
impl<T> Convert<T, T> for Identity {
	fn convert(a: T) -> T {
		a
	}
}
impl<T> ConvertBack<T, T> for Identity {
	fn convert_back(a: T) -> T {
		a
	}
}

/// A structure that performs standard conversion using the standard Rust conversion traits.
pub struct ConvertInto;
impl<A, B: From<A>> Convert<A, B> for ConvertInto {
	fn convert(a: A) -> B {
		a.into()
	}
}

/// Extensible conversion trait. Generic over both source and destination types.
pub trait ConvertBack<A, B>: Convert<A, B> {
	/// Make conversion back.
	fn convert_back(b: B) -> A;
}

/// Convenience type to work around the highly unergonomic syntax needed
/// to invoke the functions of overloaded generic traits, in this case
/// `TryFrom` and `TryInto`.
pub trait CheckedConversion {
	/// Convert from a value of `T` into an equivalent instance of `Option<Self>`.
	///
	/// This just uses `TryFrom` internally but with this
	/// variant you can provide the destination type using turbofish syntax
	/// in case Rust happens not to assume the correct type.
	fn checked_from<T>(t: T) -> Option<Self>
	where
		Self: TryFrom<T>,
	{
		<Self as TryFrom<T>>::try_from(t).ok()
	}
	/// Consume self to return `Some` equivalent value of `Option<T>`.
	///
	/// This just uses `TryInto` internally but with this
	/// variant you can provide the destination type using turbofish syntax
	/// in case Rust happens not to assume the correct type.
	fn checked_into<T>(self) -> Option<T>
	where
		Self: TryInto<T>,
	{
		<Self as TryInto<T>>::try_into(self).ok()
	}
}
impl<T: Sized> CheckedConversion for T {}

/// Multiply and divide by a number that isn't necessarily the same type. Basically just the same
/// as `Mul` and `Div` except it can be used for all basic numeric types.
pub trait Scale<Other> {
	/// The output type of the product of `self` and `Other`.
	type Output;

	/// @return the product of `self` and `other`.
	fn mul(self, other: Other) -> Self::Output;

	/// @return the integer division of `self` and `other`.
	fn div(self, other: Other) -> Self::Output;

	/// @return the modulo remainder of `self` and `other`.
	fn rem(self, other: Other) -> Self::Output;
}
macro_rules! impl_scale {
	($self:ty, $other:ty) => {
		impl Scale<$other> for $self {
			type Output = Self;
			fn mul(self, other: $other) -> Self::Output {
				self * (other as Self)
			}
			fn div(self, other: $other) -> Self::Output {
				self / (other as Self)
			}
			fn rem(self, other: $other) -> Self::Output {
				self % (other as Self)
			}
		}
	};
}
impl_scale!(u128, u128);
impl_scale!(u128, u64);
impl_scale!(u128, u32);
impl_scale!(u128, u16);
impl_scale!(u128, u8);
impl_scale!(u64, u64);
impl_scale!(u64, u32);
impl_scale!(u64, u16);
impl_scale!(u64, u8);
impl_scale!(u32, u32);
impl_scale!(u32, u16);
impl_scale!(u32, u8);
impl_scale!(u16, u16);
impl_scale!(u16, u8);
impl_scale!(u8, u8);

/// Trait for things that can be clear (have no bits set). For numeric types, essentially the same
/// as `Zero`.
pub trait Clear {
	/// True iff no bits are set.
	fn is_clear(&self) -> bool;

	/// Return the value of Self that is clear.
	fn clear() -> Self;
}

impl<T: Default + Eq + PartialEq> Clear for T {
	fn is_clear(&self) -> bool {
		*self == Self::clear()
	}
	fn clear() -> Self {
		Default::default()
	}
}

/// A meta trait for all bit ops.
pub trait SimpleBitOps:
	Sized
	+ Clear
	+ sp_std::ops::BitOr<Self, Output = Self>
	+ sp_std::ops::BitXor<Self, Output = Self>
	+ sp_std::ops::BitAnd<Self, Output = Self>
{
}
impl<
		T: Sized
			+ Clear
			+ sp_std::ops::BitOr<Self, Output = Self>
			+ sp_std::ops::BitXor<Self, Output = Self>
			+ sp_std::ops::BitAnd<Self, Output = Self>,
	> SimpleBitOps for T
{
}

/// Abstraction around hashing
// Stupid bug in the Rust compiler believes derived
// traits must be fulfilled by all type parameters.
pub trait Hash:
	'static
	+ MaybeSerializeDeserialize
	+ Debug
	+ Clone
	+ Eq
	+ PartialEq
	+ Hasher<Out = <Self as Hash>::Output>
{
	/// The hash type produced.
	type Output: Member
		+ MaybeSerializeDeserialize
		+ Debug
		+ sp_std::hash::Hash
		+ AsRef<[u8]>
		+ AsMut<[u8]>
		+ Copy
		+ Default
		+ Encode
		+ Decode
		+ MaxEncodedLen
		+ TypeInfo;

	/// Produce the hash of some byte-slice.
	fn hash(s: &[u8]) -> Self::Output {
		<Self as Hasher>::hash(s)
	}

	/// Produce the hash of some codec-encodable value.
	fn hash_of<S: Encode>(s: &S) -> Self::Output {
		Encode::using_encoded(s, <Self as Hasher>::hash)
	}

	/// The ordered Patricia tree root of the given `input`.
	fn ordered_trie_root(input: Vec<Vec<u8>>, state_version: StateVersion) -> Self::Output;

	/// The Patricia tree root of the given mapping.
	fn trie_root(input: Vec<(Vec<u8>, Vec<u8>)>, state_version: StateVersion) -> Self::Output;
}

/// Blake2-256 Hash implementation.
#[derive(PartialEq, Eq, Clone, RuntimeDebug, TypeInfo)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct BlakeTwo256;

impl Hasher for BlakeTwo256 {
	type Out = sp_core::H256;
	type StdHasher = hash256_std_hasher::Hash256StdHasher;
	const LENGTH: usize = 32;

	fn hash(s: &[u8]) -> Self::Out {
		sp_io::hashing::blake2_256(s).into()
	}
}

impl Hash for BlakeTwo256 {
	type Output = sp_core::H256;

	fn trie_root(input: Vec<(Vec<u8>, Vec<u8>)>, version: StateVersion) -> Self::Output {
		sp_io::trie::blake2_256_root(input, version)
	}

	fn ordered_trie_root(input: Vec<Vec<u8>>, version: StateVersion) -> Self::Output {
		sp_io::trie::blake2_256_ordered_root(input, version)
	}
}

/// Keccak-256 Hash implementation.
#[derive(PartialEq, Eq, Clone, RuntimeDebug, TypeInfo)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct Keccak256;

impl Hasher for Keccak256 {
	type Out = sp_core::H256;
	type StdHasher = hash256_std_hasher::Hash256StdHasher;
	const LENGTH: usize = 32;

	fn hash(s: &[u8]) -> Self::Out {
		sp_io::hashing::keccak_256(s).into()
	}
}

impl Hash for Keccak256 {
	type Output = sp_core::H256;

	fn trie_root(input: Vec<(Vec<u8>, Vec<u8>)>, version: StateVersion) -> Self::Output {
		sp_io::trie::keccak_256_root(input, version)
	}

	fn ordered_trie_root(input: Vec<Vec<u8>>, version: StateVersion) -> Self::Output {
		sp_io::trie::keccak_256_ordered_root(input, version)
	}
}

/// Something that can be checked for equality and printed out to a debug channel if bad.
pub trait CheckEqual {
	/// Perform the equality check.
	fn check_equal(&self, other: &Self);
}

impl CheckEqual for sp_core::H256 {
	#[cfg(feature = "std")]
	fn check_equal(&self, other: &Self) {
		use sp_core::hexdisplay::HexDisplay;
		if self != other {
			println!(
				"Hash: given={}, expected={}",
				HexDisplay::from(self.as_fixed_bytes()),
				HexDisplay::from(other.as_fixed_bytes()),
			);
		}
	}

	#[cfg(not(feature = "std"))]
	fn check_equal(&self, other: &Self) {
		if self != other {
			"Hash not equal".print();
			self.as_bytes().print();
			other.as_bytes().print();
		}
	}
}

impl CheckEqual for super::generic::DigestItem {
	#[cfg(feature = "std")]
	fn check_equal(&self, other: &Self) {
		if self != other {
			println!("DigestItem: given={:?}, expected={:?}", self, other);
		}
	}

	#[cfg(not(feature = "std"))]
	fn check_equal(&self, other: &Self) {
		if self != other {
			"DigestItem not equal".print();
			(&Encode::encode(self)[..]).print();
			(&Encode::encode(other)[..]).print();
		}
	}
}

sp_core::impl_maybe_marker!(
	/// A type that implements Display when in std environment.
	trait MaybeDisplay: Display;

	/// A type that implements FromStr when in std environment.
	trait MaybeFromStr: FromStr;

	/// A type that implements Hash when in std environment.
	trait MaybeHash: sp_std::hash::Hash;

	/// A type that implements Serialize when in std environment.
	trait MaybeSerialize: Serialize;

	/// A type that implements Serialize, DeserializeOwned and Debug when in std environment.
	trait MaybeSerializeDeserialize: DeserializeOwned, Serialize;
);

/// A type that can be used in runtime structures.
pub trait Member: Send + Sync + Sized + Debug + Eq + PartialEq + Clone + 'static {}
impl<T: Send + Sync + Sized + Debug + Eq + PartialEq + Clone + 'static> Member for T {}

/// Determine if a `MemberId` is a valid member.
pub trait IsMember<MemberId> {
	/// Is the given `MemberId` a valid member?
	fn is_member(member_id: &MemberId) -> bool;
}

/// Something which fulfills the abstract idea of a Substrate header. It has types for a `Number`,
/// a `Hash` and a `Hashing`. It provides access to an `extrinsics_root`, `state_root` and
/// `parent_hash`, as well as a `digest` and a block `number`.
///
/// You can also create a `new` one from those fields.
pub trait Header: Clone + Send + Sync + Codec + Eq + MaybeSerialize + Debug + 'static {
	/// Header number.
	type Number: Member
		+ MaybeSerializeDeserialize
		+ Debug
		+ sp_std::hash::Hash
		+ Copy
		+ MaybeDisplay
		+ AtLeast32BitUnsigned
		+ Codec
		+ sp_std::str::FromStr;
	/// Header hash type
	type Hash: Member
		+ MaybeSerializeDeserialize
		+ Debug
		+ sp_std::hash::Hash
		+ Ord
		+ Copy
		+ MaybeDisplay
		+ Default
		+ SimpleBitOps
		+ Codec
		+ AsRef<[u8]>
		+ AsMut<[u8]>
		+ TypeInfo;
	/// Hashing algorithm
	type Hashing: Hash<Output = Self::Hash>;

	/// Creates new header.
	fn new(
		number: Self::Number,
		extrinsics_root: Self::Hash,
		state_root: Self::Hash,
		parent_hash: Self::Hash,
		digest: Digest,
	) -> Self;

	/// Returns a reference to the header number.
	fn number(&self) -> &Self::Number;
	/// Sets the header number.
	fn set_number(&mut self, number: Self::Number);

	/// Returns a reference to the extrinsics root.
	fn extrinsics_root(&self) -> &Self::Hash;
	/// Sets the extrinsic root.
	fn set_extrinsics_root(&mut self, root: Self::Hash);

	/// Returns a reference to the state root.
	fn state_root(&self) -> &Self::Hash;
	/// Sets the state root.
	fn set_state_root(&mut self, root: Self::Hash);

	/// Returns a reference to the parent hash.
	fn parent_hash(&self) -> &Self::Hash;
	/// Sets the parent hash.
	fn set_parent_hash(&mut self, hash: Self::Hash);

	/// Returns a reference to the digest.
	fn digest(&self) -> &Digest;
	/// Get a mutable reference to the digest.
	fn digest_mut(&mut self) -> &mut Digest;

	/// Returns the hash of the header.
	fn hash(&self) -> Self::Hash {
		<Self::Hashing as Hash>::hash_of(self)
	}
}

/// Something which fulfills the abstract idea of a Substrate block. It has types for
/// `Extrinsic` pieces of information as well as a `Header`.
///
/// You can get an iterator over each of the `extrinsics` and retrieve the `header`.
pub trait Block: Clone + Send + Sync + Codec + Eq + MaybeSerialize + Debug + 'static {
	/// Type for extrinsics.
	type Extrinsic: Member + Codec + Extrinsic + MaybeSerialize;
	/// Header type.
	type Header: Header<Hash = Self::Hash>;
	/// Block hash type.
	type Hash: Member
		+ MaybeSerializeDeserialize
		+ Debug
		+ sp_std::hash::Hash
		+ Ord
		+ Copy
		+ MaybeDisplay
		+ Default
		+ SimpleBitOps
		+ Codec
		+ AsRef<[u8]>
		+ AsMut<[u8]>
		+ TypeInfo;

	/// Returns a reference to the header.
	fn header(&self) -> &Self::Header;
	/// Returns a reference to the list of extrinsics.
	fn extrinsics(&self) -> &[Self::Extrinsic];
	/// Split the block into header and list of extrinsics.
	fn deconstruct(self) -> (Self::Header, Vec<Self::Extrinsic>);
	/// Creates new block from header and extrinsics.
	fn new(header: Self::Header, extrinsics: Vec<Self::Extrinsic>) -> Self;
	/// Returns the hash of the block.
	fn hash(&self) -> Self::Hash {
		<<Self::Header as Header>::Hashing as Hash>::hash_of(self.header())
	}
	/// Creates an encoded block from the given `header` and `extrinsics` without requiring the
	/// creation of an instance.
	fn encode_from(header: &Self::Header, extrinsics: &[Self::Extrinsic]) -> Vec<u8>;
}

/// Something that acts like an `Extrinsic`.
pub trait Extrinsic: Sized {
	/// The function call.
	type Call;

	/// The payload we carry for signed extrinsics.
	///
	/// Usually it will contain a `Signature` and
	/// may include some additional data that are specific to signed
	/// extrinsics.
	type SignaturePayload;

	/// Is this `Extrinsic` signed?
	/// If no information are available about signed/unsigned, `None` should be returned.
	fn is_signed(&self) -> Option<bool> {
		None
	}

	/// Create new instance of the extrinsic.
	///
	/// Extrinsics can be split into:
	/// 1. Inherents (no signature; created by validators during block production)
	/// 2. Unsigned Transactions (no signature; represent "system calls" or other special kinds of
	/// calls) 3. Signed Transactions (with signature; a regular transactions with known origin)
	fn new(_call: Self::Call, _signed_data: Option<Self::SignaturePayload>) -> Option<Self> {
		None
	}
}

/// Implementor is an [`Extrinsic`] and provides metadata about this extrinsic.
pub trait ExtrinsicMetadata {
	/// The format version of the `Extrinsic`.
	///
	/// By format is meant the encoded representation of the `Extrinsic`.
	const VERSION: u8;

	/// Signed extensions attached to this `Extrinsic`.
	type SignedExtensions: SignedExtension;
}

/// Extract the hashing type for a block.
pub type HashFor<B> = <<B as Block>::Header as Header>::Hashing;
/// Extract the number type for a block.
pub type NumberFor<B> = <<B as Block>::Header as Header>::Number;
/// Extract the digest type for a block.

/// A "checkable" piece of information, used by the standard Substrate Executive in order to
/// check the validity of a piece of extrinsic information, usually by verifying the signature.
/// Implement for pieces of information that require some additional context `Context` in order to
/// be checked.
pub trait Checkable<Context>: Sized {
	/// Returned if `check` succeeds.
	type Checked;

	/// Check self, given an instance of Context.
	fn check(self, c: &Context) -> Result<Self::Checked, TransactionValidityError>;

	/// Blindly check self.
	///
	/// ## WARNING
	///
	/// DO NOT USE IN PRODUCTION. This is only meant to be used in testing environments. A runtime
	/// compiled with `try-runtime` should never be in production. Moreover, the name of this
	/// function is deliberately chosen to prevent developers from ever calling it in consensus
	/// code-paths.
	#[cfg(feature = "try-runtime")]
	fn unchecked_into_checked_i_know_what_i_am_doing(
		self,
		c: &Context,
	) -> Result<Self::Checked, TransactionValidityError>;
}

/// A "checkable" piece of information, used by the standard Substrate Executive in order to
/// check the validity of a piece of extrinsic information, usually by verifying the signature.
/// Implement for pieces of information that don't require additional context in order to be
/// checked.
pub trait BlindCheckable: Sized {
	/// Returned if `check` succeeds.
	type Checked;

	/// Check self.
	fn check(self) -> Result<Self::Checked, TransactionValidityError>;
}

// Every `BlindCheckable` is also a `StaticCheckable` for arbitrary `Context`.
impl<T: BlindCheckable, Context> Checkable<Context> for T {
	type Checked = <Self as BlindCheckable>::Checked;

	fn check(self, _c: &Context) -> Result<Self::Checked, TransactionValidityError> {
		BlindCheckable::check(self)
	}

	#[cfg(feature = "try-runtime")]
	fn unchecked_into_checked_i_know_what_i_am_doing(
		self,
		_: &Context,
	) -> Result<Self::Checked, TransactionValidityError> {
		unreachable!();
	}
}

/// A lazy call (module function and argument values) that can be executed via its `dispatch`
/// method.
pub trait Dispatchable {
	/// Every function call from your runtime has an origin, which specifies where the extrinsic was
	/// generated from. In the case of a signed extrinsic (transaction), the origin contains an
	/// identifier for the caller. The origin can be empty in the case of an inherent extrinsic.
	type RuntimeOrigin;
	/// ...
	type Config;
	/// An opaque set of information attached to the transaction. This could be constructed anywhere
	/// down the line in a runtime. The current Substrate runtime uses a struct with the same name
	/// to represent the dispatch class and weight.
	type Info;
	/// Additional information that is returned by `dispatch`. Can be used to supply the caller
	/// with information about a `Dispatchable` that is ownly known post dispatch.
	type PostInfo: Eq + PartialEq + Clone + Copy + Encode + Decode + Printable;
	/// Actually dispatch this call and return the result of it.
	fn dispatch(self, origin: Self::RuntimeOrigin)
		-> crate::DispatchResultWithInfo<Self::PostInfo>;
}

/// Shortcut to reference the `Info` type of a `Dispatchable`.
pub type DispatchInfoOf<T> = <T as Dispatchable>::Info;
/// Shortcut to reference the `PostInfo` type of a `Dispatchable`.
pub type PostDispatchInfoOf<T> = <T as Dispatchable>::PostInfo;

impl Dispatchable for () {
	type RuntimeOrigin = ();
	type Config = ();
	type Info = ();
	type PostInfo = ();
	fn dispatch(
		self,
		_origin: Self::RuntimeOrigin,
	) -> crate::DispatchResultWithInfo<Self::PostInfo> {
		panic!("This implementation should not be used for actual dispatch.");
	}
}

/// Means by which a transaction may be extended. This type embodies both the data and the logic
/// that should be additionally associated with the transaction. It should be plain old data.
pub trait SignedExtension:
	Codec + Debug + Sync + Send + Clone + Eq + PartialEq + StaticTypeInfo
{
	/// Unique identifier of this signed extension.
	///
	/// This will be exposed in the metadata to identify the signed extension used
	/// in an extrinsic.
	const IDENTIFIER: &'static str;

	/// The type which encodes the sender identity.
	type AccountId;

	/// The type which encodes the call to be dispatched.
	type Call: Dispatchable;

	/// Any additional data that will go into the signed payload. This may be created dynamically
	/// from the transaction using the `additional_signed` function.
	type AdditionalSigned: Encode + TypeInfo;

	/// The type that encodes information that can be passed from pre_dispatch to post-dispatch.
	type Pre;

	/// Construct any additional data that should be in the signed payload of the transaction. Can
	/// also perform any pre-signature-verification checks and return an error if needed.
	fn additional_signed(&self) -> Result<Self::AdditionalSigned, TransactionValidityError>;

	/// Validate a signed transaction for the transaction queue.
	///
	/// This function can be called frequently by the transaction queue,
	/// to obtain transaction validity against current state.
	/// It should perform all checks that determine a valid transaction,
	/// that can pay for its execution and quickly eliminate ones
	/// that are stale or incorrect.
	///
	/// Make sure to perform the same checks in `pre_dispatch` function.
	fn validate(
		&self,
		_who: &Self::AccountId,
		_call: &Self::Call,
		_info: &DispatchInfoOf<Self::Call>,
		_len: usize,
	) -> TransactionValidity {
		Ok(ValidTransaction::default())
	}

	/// Do any pre-flight stuff for a signed transaction.
	///
	/// Make sure to perform the same checks as in [`Self::validate`].
	fn pre_dispatch(
		self,
		who: &Self::AccountId,
		call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> Result<Self::Pre, TransactionValidityError>;

	/// Validate an unsigned transaction for the transaction queue.
	///
	/// This function can be called frequently by the transaction queue
	/// to obtain transaction validity against current state.
	/// It should perform all checks that determine a valid unsigned transaction,
	/// and quickly eliminate ones that are stale or incorrect.
	///
	/// Make sure to perform the same checks in `pre_dispatch_unsigned` function.
	fn validate_unsigned(
		_call: &Self::Call,
		_info: &DispatchInfoOf<Self::Call>,
		_len: usize,
	) -> TransactionValidity {
		Ok(ValidTransaction::default())
	}

	/// Do any pre-flight stuff for a unsigned transaction.
	///
	/// Note this function by default delegates to `validate_unsigned`, so that
	/// all checks performed for the transaction queue are also performed during
	/// the dispatch phase (applying the extrinsic).
	///
	/// If you ever override this function, you need to make sure to always
	/// perform the same validation as in `validate_unsigned`.
	fn pre_dispatch_unsigned(
		call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> Result<(), TransactionValidityError> {
		Self::validate_unsigned(call, info, len).map(|_| ()).map_err(Into::into)
	}

	/// Do any post-flight stuff for an extrinsic.
	///
	/// If the transaction is signed, then `_pre` will contain the output of `pre_dispatch`,
	/// and `None` otherwise.
	///
	/// This gets given the `DispatchResult` `_result` from the extrinsic and can, if desired,
	/// introduce a `TransactionValidityError`, causing the block to become invalid for including
	/// it.
	///
	/// WARNING: It is dangerous to return an error here. To do so will fundamentally invalidate the
	/// transaction and any block that it is included in, causing the block author to not be
	/// compensated for their work in validating the transaction or producing the block so far.
	///
	/// It can only be used safely when you *know* that the extrinsic is one that can only be
	/// introduced by the current block author; generally this implies that it is an inherent and
	/// will come from either an offchain-worker or via `InherentData`.
	fn post_dispatch(
		_pre: Option<Self::Pre>,
		_info: &DispatchInfoOf<Self::Call>,
		_post_info: &PostDispatchInfoOf<Self::Call>,
		_len: usize,
		_result: &DispatchResult,
	) -> Result<(), TransactionValidityError> {
		Ok(())
	}

	/// Returns the metadata for this signed extension.
	///
	/// As a [`SignedExtension`] can be a tuple of [`SignedExtension`]s we need to return a `Vec`
	/// that holds the metadata of each one. Each individual `SignedExtension` must return
	/// *exactly* one [`SignedExtensionMetadata`].
	///
	/// This method provides a default implementation that returns a vec containing a single
	/// [`SignedExtensionMetadata`].
	fn metadata() -> Vec<SignedExtensionMetadata> {
		sp_std::vec![SignedExtensionMetadata {
			identifier: Self::IDENTIFIER,
			ty: scale_info::meta_type::<Self>(),
			additional_signed: scale_info::meta_type::<Self::AdditionalSigned>()
		}]
	}
}

/// Information about a [`SignedExtension`] for the runtime metadata.
pub struct SignedExtensionMetadata {
	/// The unique identifier of the [`SignedExtension`].
	pub identifier: &'static str,
	/// The type of the [`SignedExtension`].
	pub ty: MetaType,
	/// The type of the [`SignedExtension`] additional signed data for the payload.
	pub additional_signed: MetaType,
}

#[impl_for_tuples(1, 12)]
impl<AccountId, Call: Dispatchable> SignedExtension for Tuple {
	for_tuples!( where #( Tuple: SignedExtension<AccountId=AccountId, Call=Call,> )* );
	type AccountId = AccountId;
	type Call = Call;
	const IDENTIFIER: &'static str = "You should call `identifier()`!";
	for_tuples!( type AdditionalSigned = ( #( Tuple::AdditionalSigned ),* ); );
	for_tuples!( type Pre = ( #( Tuple::Pre ),* ); );

	fn additional_signed(&self) -> Result<Self::AdditionalSigned, TransactionValidityError> {
		Ok(for_tuples!( ( #( Tuple.additional_signed()? ),* ) ))
	}

	fn validate(
		&self,
		who: &Self::AccountId,
		call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> TransactionValidity {
		let valid = ValidTransaction::default();
		for_tuples!( #( let valid = valid.combine_with(Tuple.validate(who, call, info, len)?); )* );
		Ok(valid)
	}

	fn pre_dispatch(
		self,
		who: &Self::AccountId,
		call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> Result<Self::Pre, TransactionValidityError> {
		Ok(for_tuples!( ( #( Tuple.pre_dispatch(who, call, info, len)? ),* ) ))
	}

	fn validate_unsigned(
		call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> TransactionValidity {
		let valid = ValidTransaction::default();
		for_tuples!( #( let valid = valid.combine_with(Tuple::validate_unsigned(call, info, len)?); )* );
		Ok(valid)
	}

	fn pre_dispatch_unsigned(
		call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> Result<(), TransactionValidityError> {
		for_tuples!( #( Tuple::pre_dispatch_unsigned(call, info, len)?; )* );
		Ok(())
	}

	fn post_dispatch(
		pre: Option<Self::Pre>,
		info: &DispatchInfoOf<Self::Call>,
		post_info: &PostDispatchInfoOf<Self::Call>,
		len: usize,
		result: &DispatchResult,
	) -> Result<(), TransactionValidityError> {
		match pre {
			Some(x) => {
				for_tuples!( #( Tuple::post_dispatch(Some(x.Tuple), info, post_info, len, result)?; )* );
			},
			None => {
				for_tuples!( #( Tuple::post_dispatch(None, info, post_info, len, result)?; )* );
			},
		}
		Ok(())
	}

	fn metadata() -> Vec<SignedExtensionMetadata> {
		let mut ids = Vec::new();
		for_tuples!( #( ids.extend(Tuple::metadata()); )* );
		ids
	}
}

/// Only for bare bone testing when you don't care about signed extensions at all.
#[cfg(feature = "std")]
impl SignedExtension for () {
	type AccountId = u64;
	type AdditionalSigned = ();
	type Call = ();
	type Pre = ();
	const IDENTIFIER: &'static str = "UnitSignedExtension";
	fn additional_signed(&self) -> sp_std::result::Result<(), TransactionValidityError> {
		Ok(())
	}
	fn pre_dispatch(
		self,
		who: &Self::AccountId,
		call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> Result<Self::Pre, TransactionValidityError> {
		self.validate(who, call, info, len).map(|_| ())
	}
}

/// An "executable" piece of information, used by the standard Substrate Executive in order to
/// enact a piece of extrinsic information by marshalling and dispatching to a named function
/// call.
///
/// Also provides information on to whom this information is attributable and an index that allows
/// each piece of attributable information to be disambiguated.
pub trait Applyable: Sized + Send + Sync {
	/// Type by which we can dispatch. Restricts the `UnsignedValidator` type.
	type Call: Dispatchable;

	/// Checks to see if this is a valid *transaction*. It returns information on it if so.
	fn validate<V: ValidateUnsigned<Call = Self::Call>>(
		&self,
		source: TransactionSource,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> TransactionValidity;

	/// Executes all necessary logic needed prior to dispatch and deconstructs into function call,
	/// index and sender.
	fn apply<V: ValidateUnsigned<Call = Self::Call>>(
		self,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> crate::ApplyExtrinsicResultWithInfo<PostDispatchInfoOf<Self::Call>>;
}

/// A marker trait for something that knows the type of the runtime block.
pub trait GetRuntimeBlockType {
	/// The `RuntimeBlock` type.
	type RuntimeBlock: self::Block;
}

/// A marker trait for something that knows the type of the node block.
pub trait GetNodeBlockType {
	/// The `NodeBlock` type.
	type NodeBlock: self::Block;
}

/// Provide validation for unsigned extrinsics.
///
/// This trait provides two functions [`pre_dispatch`](Self::pre_dispatch) and
/// [`validate_unsigned`](Self::validate_unsigned). The [`pre_dispatch`](Self::pre_dispatch)
/// function is called right before dispatching the call wrapped by an unsigned extrinsic. The
/// [`validate_unsigned`](Self::validate_unsigned) function is mainly being used in the context of
/// the transaction pool to check the validity of the call wrapped by an unsigned extrinsic.
pub trait ValidateUnsigned {
	/// The call to validate
	type Call;

	/// Validate the call right before dispatch.
	///
	/// This method should be used to prevent transactions already in the pool
	/// (i.e. passing [`validate_unsigned`](Self::validate_unsigned)) from being included in blocks
	/// in case they became invalid since being added to the pool.
	///
	/// By default it's a good idea to call [`validate_unsigned`](Self::validate_unsigned) from
	/// within this function again to make sure we never include an invalid transaction. Otherwise
	/// the implementation of the call or this method will need to provide proper validation to
	/// ensure that the transaction is valid.
	///
	/// Changes made to storage *WILL* be persisted if the call returns `Ok`.
	fn pre_dispatch(call: &Self::Call) -> Result<(), TransactionValidityError> {
		Self::validate_unsigned(TransactionSource::InBlock, call)
			.map(|_| ())
			.map_err(Into::into)
	}

	/// Return the validity of the call
	///
	/// This method has no side-effects. It merely checks whether the call would be rejected
	/// by the runtime in an unsigned extrinsic.
	///
	/// The validity checks should be as lightweight as possible because every node will execute
	/// this code before the unsigned extrinsic enters the transaction pool and also periodically
	/// afterwards to ensure the validity. To prevent dos-ing a network with unsigned
	/// extrinsics, these validity checks should include some checks around uniqueness, for example,
	/// like checking that the unsigned extrinsic was send by an authority in the active set.
	///
	/// Changes made to storage should be discarded by caller.
	fn validate_unsigned(source: TransactionSource, call: &Self::Call) -> TransactionValidity;
}

/// Opaque data type that may be destructured into a series of raw byte slices (which represent
/// individual keys).
pub trait OpaqueKeys: Clone {
	/// Types bound to this opaque keys that provide the key type ids returned.
	type KeyTypeIdProviders;

	/// Return the key-type IDs supported by this set.
	fn key_ids() -> &'static [crate::KeyTypeId];
	/// Get the raw bytes of key with key-type ID `i`.
	fn get_raw(&self, i: super::KeyTypeId) -> &[u8];
	/// Get the decoded key with key-type ID `i`.
	fn get<T: Decode>(&self, i: super::KeyTypeId) -> Option<T> {
		T::decode(&mut self.get_raw(i)).ok()
	}
	/// Verify a proof of ownership for the keys.
	fn ownership_proof_is_valid(&self, _proof: &[u8]) -> bool {
		true
	}
}

/// Input that adds infinite number of zero after wrapped input.
///
/// This can add an infinite stream of zeros onto any input, not just a slice as with
/// `TrailingZerosInput`.
pub struct AppendZerosInput<'a, T>(&'a mut T);

impl<'a, T> AppendZerosInput<'a, T> {
	/// Create a new instance from the given byte array.
	pub fn new(input: &'a mut T) -> Self {
		Self(input)
	}
}

impl<'a, T: codec::Input> codec::Input for AppendZerosInput<'a, T> {
	fn remaining_len(&mut self) -> Result<Option<usize>, codec::Error> {
		Ok(None)
	}

	fn read(&mut self, into: &mut [u8]) -> Result<(), codec::Error> {
		let remaining = self.0.remaining_len()?;
		let completed = if let Some(n) = remaining {
			let readable = into.len().min(n);
			// this should never fail if `remaining_len` API is implemented correctly.
			self.0.read(&mut into[..readable])?;
			readable
		} else {
			// Fill it byte-by-byte.
			let mut i = 0;
			while i < into.len() {
				if let Ok(b) = self.0.read_byte() {
					into[i] = b;
					i += 1;
				} else {
					break
				}
			}
			i
		};
		// Fill the rest with zeros.
		for i in &mut into[completed..] {
			*i = 0;
		}
		Ok(())
	}
}

/// Input that adds infinite number of zero after wrapped input.
pub struct TrailingZeroInput<'a>(&'a [u8]);

impl<'a> TrailingZeroInput<'a> {
	/// Create a new instance from the given byte array.
	pub fn new(data: &'a [u8]) -> Self {
		Self(data)
	}

	/// Create a new instance which only contains zeroes as input.
	pub fn zeroes() -> Self {
		Self::new(&[][..])
	}
}

impl<'a> codec::Input for TrailingZeroInput<'a> {
	fn remaining_len(&mut self) -> Result<Option<usize>, codec::Error> {
		Ok(None)
	}

	fn read(&mut self, into: &mut [u8]) -> Result<(), codec::Error> {
		let len_from_inner = into.len().min(self.0.len());
		into[..len_from_inner].copy_from_slice(&self.0[..len_from_inner]);
		for i in &mut into[len_from_inner..] {
			*i = 0;
		}
		self.0 = &self.0[len_from_inner..];

		Ok(())
	}
}

/// This type can be converted into and possibly from an AccountId (which itself is generic).
pub trait AccountIdConversion<AccountId>: Sized {
	/// Convert into an account ID. This is infallible, and may truncate bytes to provide a result.
	/// This may lead to duplicate accounts if the size of `AccountId` is less than the seed.
	fn into_account_truncating(&self) -> AccountId {
		self.into_sub_account_truncating(&())
	}

	/// Convert into an account ID, checking that all bytes of the seed are being used in the final
	/// `AccountId` generated. If any bytes are dropped, this returns `None`.
	fn try_into_account(&self) -> Option<AccountId> {
		self.try_into_sub_account(&())
	}

	/// Try to convert an account ID into this type. Might not succeed.
	fn try_from_account(a: &AccountId) -> Option<Self> {
		Self::try_from_sub_account::<()>(a).map(|x| x.0)
	}

	/// Convert this value amalgamated with the a secondary "sub" value into an account ID,
	/// truncating any unused bytes. This is infallible.
	///
	/// NOTE: The account IDs from this and from `into_account` are *not* guaranteed to be distinct
	/// for any given value of `self`, nor are different invocations to this with different types
	/// `T`. For example, the following will all encode to the same account ID value:
	/// - `self.into_sub_account(0u32)`
	/// - `self.into_sub_account(vec![0u8; 0])`
	/// - `self.into_account()`
	///
	/// Also, if the seed provided to this function is greater than the number of bytes which fit
	/// into this `AccountId` type, then it will lead to truncation of the seed, and potentially
	/// non-unique accounts.
	fn into_sub_account_truncating<S: Encode>(&self, sub: S) -> AccountId;

	/// Same as `into_sub_account_truncating`, but ensuring that all bytes of the account's seed are
	/// used when generating an account. This can help guarantee that different accounts are unique,
	/// besides types which encode the same as noted above.
	fn try_into_sub_account<S: Encode>(&self, sub: S) -> Option<AccountId>;

	/// Try to convert an account ID into this type. Might not succeed.
	fn try_from_sub_account<S: Decode>(x: &AccountId) -> Option<(Self, S)>;
}

/// Format is TYPE_ID ++ encode(sub-seed) ++ 00.... where 00... is indefinite trailing zeroes to
/// fill AccountId.
impl<T: Encode + Decode, Id: Encode + Decode + TypeId> AccountIdConversion<T> for Id {
	// Take the `sub` seed, and put as much of it as possible into the generated account, but
	// allowing truncation of the seed if it would not fit into the account id in full. This can
	// lead to two different `sub` seeds with the same account generated.
	fn into_sub_account_truncating<S: Encode>(&self, sub: S) -> T {
		(Id::TYPE_ID, self, sub)
			.using_encoded(|b| T::decode(&mut TrailingZeroInput(b)))
			.expect("All byte sequences are valid `AccountIds`; qed")
	}

	// Same as `into_sub_account_truncating`, but returns `None` if any bytes would be truncated.
	fn try_into_sub_account<S: Encode>(&self, sub: S) -> Option<T> {
		let encoded_seed = (Id::TYPE_ID, self, sub).encode();
		let account = T::decode(&mut TrailingZeroInput(&encoded_seed))
			.expect("All byte sequences are valid `AccountIds`; qed");
		// If the `account` generated has less bytes than the `encoded_seed`, then we know that
		// bytes were truncated, and we return `None`.
		if encoded_seed.len() <= account.encoded_size() {
			Some(account)
		} else {
			None
		}
	}

	fn try_from_sub_account<S: Decode>(x: &T) -> Option<(Self, S)> {
		x.using_encoded(|d| {
			if d[0..4] != Id::TYPE_ID {
				return None
			}
			let mut cursor = &d[4..];
			let result = Decode::decode(&mut cursor).ok()?;
			if cursor.iter().all(|x| *x == 0) {
				Some(result)
			} else {
				None
			}
		})
	}
}

/// Calls a given macro a number of times with a set of fixed params and an incrementing numeral.
/// e.g.
/// ```nocompile
/// count!(println ("{}",) foo, bar, baz);
/// // Will result in three `println!`s: "0", "1" and "2".
/// ```
#[macro_export]
macro_rules! count {
	($f:ident ($($x:tt)*) ) => ();
	($f:ident ($($x:tt)*) $x1:tt) => { $f!($($x)* 0); };
	($f:ident ($($x:tt)*) $x1:tt, $x2:tt) => { $f!($($x)* 0); $f!($($x)* 1); };
	($f:ident ($($x:tt)*) $x1:tt, $x2:tt, $x3:tt) => { $f!($($x)* 0); $f!($($x)* 1); $f!($($x)* 2); };
	($f:ident ($($x:tt)*) $x1:tt, $x2:tt, $x3:tt, $x4:tt) => {
		$f!($($x)* 0); $f!($($x)* 1); $f!($($x)* 2); $f!($($x)* 3);
	};
	($f:ident ($($x:tt)*) $x1:tt, $x2:tt, $x3:tt, $x4:tt, $x5:tt) => {
		$f!($($x)* 0); $f!($($x)* 1); $f!($($x)* 2); $f!($($x)* 3); $f!($($x)* 4);
	};
}

#[doc(hidden)]
#[macro_export]
macro_rules! impl_opaque_keys_inner {
	(
		$( #[ $attr:meta ] )*
		pub struct $name:ident {
			$(
				$( #[ $inner_attr:meta ] )*
				pub $field:ident: $type:ty,
			)*
		}
	) => {
		$( #[ $attr ] )*
		#[derive(
			Clone, PartialEq, Eq,
			$crate::codec::Encode,
			$crate::codec::Decode,
			$crate::scale_info::TypeInfo,
			$crate::RuntimeDebug,
		)]
		pub struct $name {
			$(
				$( #[ $inner_attr ] )*
				pub $field: <$type as $crate::BoundToRuntimeAppPublic>::Public,
			)*
		}

		impl $name {
			/// Generate a set of keys with optionally using the given seed.
			///
			/// The generated key pairs are stored in the keystore.
			///
			/// Returns the concatenated SCALE encoded public keys.
			pub fn generate(seed: Option<$crate::sp_std::vec::Vec<u8>>) -> $crate::sp_std::vec::Vec<u8> {
				let keys = Self{
					$(
						$field: <
							<
								$type as $crate::BoundToRuntimeAppPublic
							>::Public as $crate::RuntimeAppPublic
						>::generate_pair(seed.clone()),
					)*
				};
				$crate::codec::Encode::encode(&keys)
			}

			/// Converts `Self` into a `Vec` of `(raw public key, KeyTypeId)`.
			pub fn into_raw_public_keys(
				self,
			) -> $crate::sp_std::vec::Vec<($crate::sp_std::vec::Vec<u8>, $crate::KeyTypeId)> {
				let mut keys = Vec::new();
				$(
					keys.push((
						$crate::RuntimeAppPublic::to_raw_vec(&self.$field),
						<
							<
								$type as $crate::BoundToRuntimeAppPublic
							>::Public as $crate::RuntimeAppPublic
						>::ID,
					));
				)*

				keys
			}

			/// Decode `Self` from the given `encoded` slice and convert `Self` into the raw public
			/// keys (see [`Self::into_raw_public_keys`]).
			///
			/// Returns `None` when the decoding failed, otherwise `Some(_)`.
			pub fn decode_into_raw_public_keys(
				encoded: &[u8],
			) -> Option<$crate::sp_std::vec::Vec<($crate::sp_std::vec::Vec<u8>, $crate::KeyTypeId)>> {
				<Self as $crate::codec::Decode>::decode(&mut &encoded[..])
					.ok()
					.map(|s| s.into_raw_public_keys())
			}
		}

		impl $crate::traits::OpaqueKeys for $name {
			type KeyTypeIdProviders = ( $( $type, )* );

			fn key_ids() -> &'static [$crate::KeyTypeId] {
				&[
					$(
						<
							<
								$type as $crate::BoundToRuntimeAppPublic
							>::Public as $crate::RuntimeAppPublic
						>::ID
					),*
				]
			}

			fn get_raw(&self, i: $crate::KeyTypeId) -> &[u8] {
				match i {
					$(
						i if i == <
							<
								$type as $crate::BoundToRuntimeAppPublic
							>::Public as $crate::RuntimeAppPublic
						>::ID =>
							self.$field.as_ref(),
					)*
					_ => &[],
				}
			}
		}
	};
}

/// Implement `OpaqueKeys` for a described struct.
///
/// Every field type must implement [`BoundToRuntimeAppPublic`](crate::BoundToRuntimeAppPublic).
/// `KeyTypeIdProviders` is set to the types given as fields.
///
/// ```rust
/// use sp_runtime::{
/// 	impl_opaque_keys, KeyTypeId, BoundToRuntimeAppPublic, app_crypto::{sr25519, ed25519}
/// };
///
/// pub struct KeyModule;
/// impl BoundToRuntimeAppPublic for KeyModule { type Public = ed25519::AppPublic; }
///
/// pub struct KeyModule2;
/// impl BoundToRuntimeAppPublic for KeyModule2 { type Public = sr25519::AppPublic; }
///
/// impl_opaque_keys! {
/// 	pub struct Keys {
/// 		pub key_module: KeyModule,
/// 		pub key_module2: KeyModule2,
/// 	}
/// }
/// ```
#[macro_export]
#[cfg(feature = "std")]
macro_rules! impl_opaque_keys {
	{
		$( #[ $attr:meta ] )*
		pub struct $name:ident {
			$(
				$( #[ $inner_attr:meta ] )*
				pub $field:ident: $type:ty,
			)*
		}
	} => {
		$crate::paste::paste! {
			use $crate::serde as [< __opaque_keys_serde_import__ $name >];

			$crate::impl_opaque_keys_inner! {
				$( #[ $attr ] )*
				#[derive($crate::serde::Serialize, $crate::serde::Deserialize)]
				#[serde(crate = "__opaque_keys_serde_import__" $name)]
				pub struct $name {
					$(
						$( #[ $inner_attr ] )*
						pub $field: $type,
					)*
				}
			}
		}
	}
}

#[macro_export]
#[cfg(not(feature = "std"))]
#[doc(hidden)]
macro_rules! impl_opaque_keys {
	{
		$( #[ $attr:meta ] )*
		pub struct $name:ident {
			$(
				$( #[ $inner_attr:meta ] )*
				pub $field:ident: $type:ty,
			)*
		}
	} => {
		$crate::impl_opaque_keys_inner! {
			$( #[ $attr ] )*
			pub struct $name {
				$(
					$( #[ $inner_attr ] )*
					pub $field: $type,
				)*
			}
		}
	}
}

/// Trait for things which can be printed from the runtime.
pub trait Printable {
	/// Print the object.
	fn print(&self);
}

impl<T: Printable> Printable for &T {
	fn print(&self) {
		(*self).print()
	}
}

impl Printable for u8 {
	fn print(&self) {
		(*self as u64).print()
	}
}

impl Printable for u32 {
	fn print(&self) {
		(*self as u64).print()
	}
}

impl Printable for usize {
	fn print(&self) {
		(*self as u64).print()
	}
}

impl Printable for u64 {
	fn print(&self) {
		sp_io::misc::print_num(*self);
	}
}

impl Printable for &[u8] {
	fn print(&self) {
		sp_io::misc::print_hex(self);
	}
}

impl<const N: usize> Printable for [u8; N] {
	fn print(&self) {
		sp_io::misc::print_hex(&self[..]);
	}
}

impl Printable for &str {
	fn print(&self) {
		sp_io::misc::print_utf8(self.as_bytes());
	}
}

impl Printable for bool {
	fn print(&self) {
		if *self {
			"true".print()
		} else {
			"false".print()
		}
	}
}

impl Printable for sp_weights::Weight {
	fn print(&self) {
		self.ref_time().print()
	}
}

impl Printable for () {
	fn print(&self) {
		"()".print()
	}
}

#[impl_for_tuples(1, 12)]
impl Printable for Tuple {
	fn print(&self) {
		for_tuples!( #( Tuple.print(); )* )
	}
}

/// Something that can convert a [`BlockId`](crate::generic::BlockId) to a number or a hash.
#[cfg(feature = "std")]
pub trait BlockIdTo<Block: self::Block> {
	/// The error type that will be returned by the functions.
	type Error: std::error::Error;

	/// Convert the given `block_id` to the corresponding block hash.
	fn to_hash(
		&self,
		block_id: &crate::generic::BlockId<Block>,
	) -> Result<Option<Block::Hash>, Self::Error>;

	/// Convert the given `block_id` to the corresponding block number.
	fn to_number(
		&self,
		block_id: &crate::generic::BlockId<Block>,
	) -> Result<Option<NumberFor<Block>>, Self::Error>;
}

/// Get current block number
pub trait BlockNumberProvider {
	/// Type of `BlockNumber` to provide.
	type BlockNumber: Codec + Clone + Ord + Eq + AtLeast32BitUnsigned;

	/// Returns the current block number.
	///
	/// Provides an abstraction over an arbitrary way of providing the
	/// current block number.
	///
	/// In case of using crate `sp_runtime` with the crate `frame-system`,
	/// it is already implemented for
	/// `frame_system::Pallet<T: Config>` as:
	///
	/// ```ignore
	/// fn current_block_number() -> Self {
	///     frame_system::Pallet<Config>::block_number()
	/// }
	/// ```
	/// .
	fn current_block_number() -> Self::BlockNumber;

	/// Utility function only to be used in benchmarking scenarios, to be implemented optionally,
	/// else a noop.
	///
	/// It allows for setting the block number that will later be fetched
	/// This is useful in case the block number provider is different than System
	#[cfg(feature = "runtime-benchmarks")]
	fn set_block_number(_block: Self::BlockNumber) {}
}

/// Arithmetic operations with safe error handling.
///
/// This module provide a readable way to do safe arithmetics, turning this:
///
/// ```ignore
/// self.my_value = self.my_value.checked_sub(other_value).ok_or(ArithmeticError::Overflow)?;
/// ```
///
/// into this:
///
/// ```ignore
/// self.my_value.ensure_sub_assign(other_value)?;
/// ```
///
/// choosing the correct [`ArithmeticError`] it should return in case of fail.
///
/// The *EnsureOps* family functions follows the same behavior as *CheckedOps* but
/// returning an [`ArithmeticError`] instead of `None`.
///
/// [`ArithmeticError`]: crate::ArithmeticError
pub mod ensure {
	use crate::ArithmeticError;
	use sp_arithmetic::{
		traits::{CheckedAdd, CheckedDiv, CheckedMul, CheckedSub, Zero},
		FixedPointNumber, FixedPointOperand,
	};

	/// Performs addition that returns `ArithmeticError` instead of wrapping around on overflow.
	pub trait EnsureAdd: CheckedAdd + PartialOrd + Zero + Copy {
		/// Adds two numbers, checking for overflow.
		/// If overflow happens, `ArithmeticError` is returned.
		///
		/// Similar to [`CheckedAdd::checked_add()`] but returning an `ArithmeticError` error
		///
		/// ```
		/// use sp_runtime::traits::ensure::EnsureAdd;
		/// use sp_runtime::{DispatchResult, ArithmeticError, DispatchError};
		///
		/// fn extrinsic_overflow() -> DispatchResult {
		///     u32::MAX.ensure_add(1)?;
		///     Ok(())
		/// }
		///
		/// fn extrinsic_underflow() -> DispatchResult {
		///     i32::MIN.ensure_add(-1)?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(extrinsic_overflow(), Err(ArithmeticError::Overflow.into()));
		/// assert_eq!(extrinsic_underflow(), Err(ArithmeticError::Underflow.into()));
		/// ```
		fn ensure_add(self, v: Self) -> Result<Self, ArithmeticError> {
			self.checked_add(&v).ok_or_else(|| error::equivalent(v))
		}
	}

	/// Performs subtraction that returns `ArithmeticError` instead of wrapping around on underflow.
	pub trait EnsureSub: CheckedSub + PartialOrd + Zero + Copy {
		/// Subtracts two numbers, checking for overflow.
		/// If overflow happens, `ArithmeticError` is returned.
		///
		/// Similar to [`CheckedSub::checked_sub()`] but returning an `ArithmeticError` error
		///
		/// ```
		/// use sp_runtime::traits::ensure::EnsureSub;
		/// use sp_runtime::{DispatchResult, ArithmeticError, DispatchError};
		///
		/// fn extrinsic_underflow() -> DispatchResult {
		///     0u32.ensure_sub(1)?;
		///     Ok(())
		/// }
		///
		/// fn extrinsic_overflow() -> DispatchResult {
		///     i32::MAX.ensure_sub(-1)?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(extrinsic_underflow(), Err(ArithmeticError::Underflow.into()));
		/// assert_eq!(extrinsic_overflow(), Err(ArithmeticError::Overflow.into()));
		/// ```
		fn ensure_sub(self, v: Self) -> Result<Self, ArithmeticError> {
			self.checked_sub(&v).ok_or_else(|| error::inverse(v))
		}
	}

	/// Performs multiplication that returns `ArithmeticError` instead of wrapping around on
	/// overflow.
	pub trait EnsureMul: CheckedMul + PartialOrd + Zero + Copy {
		/// Multiplies two numbers, checking for overflow. If overflow happens,
		/// `ArithmeticError` is returned.
		///
		/// Similar to [`CheckedMul::checked_mul()`] but returning an `ArithmeticError` error
		///
		/// ```
		/// use sp_runtime::traits::ensure::EnsureMul;
		/// use sp_runtime::{DispatchResult, ArithmeticError, DispatchError};
		///
		/// fn extrinsic_overflow() -> DispatchResult {
		///     u32::MAX.ensure_mul(2)?;
		///     Ok(())
		/// }
		///
		/// fn extrinsic_underflow() -> DispatchResult {
		///     i32::MAX.ensure_mul(-2)?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(extrinsic_overflow(), Err(ArithmeticError::Overflow.into()));
		/// assert_eq!(extrinsic_underflow(), Err(ArithmeticError::Underflow.into()));
		/// ```
		fn ensure_mul(self, v: Self) -> Result<Self, ArithmeticError> {
			self.checked_mul(&v).ok_or_else(|| error::multiplication(self, v))
		}
	}

	/// Performs division that returns `ArithmeticError` instead of wrapping around on overflow.
	pub trait EnsureDiv: CheckedDiv + PartialOrd + Zero + Copy {
		/// Divides two numbers, checking for overflow.
		/// If overflow happens, `ArithmeticError` is returned.
		///
		/// Similar to [`CheckedDiv::checked_div()`] but returning an `ArithmeticError` error
		///
		/// ```
		/// use sp_runtime::traits::ensure::EnsureDiv;
		/// use sp_runtime::{DispatchResult, ArithmeticError, DispatchError, FixedI64};
		///
		/// fn extrinsic_zero() -> DispatchResult {
		///     1.ensure_div(0)?;
		///     Ok(())
		/// }
		///
		/// fn extrinsic_overflow() -> DispatchResult {
		///     FixedI64::from(i64::MIN).ensure_div(FixedI64::from(-1))?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(extrinsic_zero(), Err(ArithmeticError::DivisionByZero.into()));
		/// assert_eq!(extrinsic_overflow(), Err(ArithmeticError::Overflow.into()));
		/// ```
		fn ensure_div(self, v: Self) -> Result<Self, ArithmeticError> {
			self.checked_div(&v).ok_or_else(|| error::division(self, v))
		}
	}

	impl<T: CheckedAdd + PartialOrd + Zero + Copy> EnsureAdd for T {}
	impl<T: CheckedSub + PartialOrd + Zero + Copy> EnsureSub for T {}
	impl<T: CheckedMul + PartialOrd + Zero + Copy> EnsureMul for T {}
	impl<T: CheckedDiv + PartialOrd + Zero + Copy> EnsureDiv for T {}

	/// Meta trait that supports all arithmetic operations
	pub trait EnsureOp: EnsureAdd + EnsureSub + EnsureMul + EnsureDiv {}
	impl<T: EnsureAdd + EnsureSub + EnsureMul + EnsureDiv> EnsureOp for T {}

	/// Performs self addition that returns `ArithmeticError` instead of wrapping around on
	/// overflow.
	pub trait EnsureAddAssign: EnsureAdd {
		/// Adds two numbers overwriting the left hand one, checking for overflow.
		/// If overflow happens, `ArithmeticError` is returned.
		///
		/// ```
		/// use sp_runtime::traits::ensure::EnsureAddAssign;
		/// use sp_runtime::{DispatchResult, ArithmeticError, DispatchError};
		///
		/// fn extrinsic_overflow() -> DispatchResult {
		///     let mut max = u32::MAX;
		///     max.ensure_add_assign(1)?;
		///     Ok(())
		/// }
		///
		/// fn extrinsic_underflow() -> DispatchResult {
		///     let mut max = i32::MIN;
		///     max.ensure_add_assign(-1)?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(extrinsic_overflow(), Err(ArithmeticError::Overflow.into()));
		/// assert_eq!(extrinsic_underflow(), Err(ArithmeticError::Underflow.into()));
		/// ```
		fn ensure_add_assign(&mut self, v: Self) -> Result<&mut Self, ArithmeticError> {
			*self = self.ensure_add(v)?;
			Ok(self)
		}
	}

	/// Performs self subtraction that returns `ArithmeticError` instead of wrapping around on
	/// underflow.
	pub trait EnsureSubAssign: EnsureSub {
		/// Subtracts two numbers overwriting the left hand one, checking for overflow.
		/// If overflow happens, `ArithmeticError` is returned.
		///
		/// ```
		/// use sp_runtime::traits::ensure::EnsureSubAssign;
		/// use sp_runtime::{DispatchResult, ArithmeticError, DispatchError};
		///
		/// fn extrinsic_underflow() -> DispatchResult {
		///     let mut zero: u32 = 0;
		///     zero.ensure_sub_assign(1)?;
		///     Ok(())
		/// }
		///
		/// fn extrinsic_overflow() -> DispatchResult {
		///     let mut zero = i32::MAX;
		///     zero.ensure_sub_assign(-1)?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(extrinsic_underflow(), Err(ArithmeticError::Underflow.into()));
		/// assert_eq!(extrinsic_overflow(), Err(ArithmeticError::Overflow.into()));
		/// ```
		fn ensure_sub_assign(&mut self, v: Self) -> Result<&mut Self, ArithmeticError> {
			*self = self.ensure_sub(v)?;
			Ok(self)
		}
	}

	/// Performs self multiplication that returns `ArithmeticError` instead of wrapping around on
	/// overflow.
	pub trait EnsureMulAssign: EnsureMul {
		/// Multiplies two numbers overwriting the left hand one, checking for overflow.
		/// If overflow happens, `ArithmeticError` is returned.
		///
		/// ```
		/// use sp_runtime::traits::ensure::EnsureMulAssign;
		/// use sp_runtime::{DispatchResult, ArithmeticError, DispatchError};
		///
		/// fn extrinsic_overflow() -> DispatchResult {
		///     let mut max = u32::MAX;
		///     max.ensure_mul_assign(2)?;
		///     Ok(())
		/// }
		///
		/// fn extrinsic_underflow() -> DispatchResult {
		///     let mut max = i32::MAX;
		///     max.ensure_mul_assign(-2)?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(extrinsic_overflow(), Err(ArithmeticError::Overflow.into()));
		/// assert_eq!(extrinsic_underflow(), Err(ArithmeticError::Underflow.into()));
		/// ```
		fn ensure_mul_assign(&mut self, v: Self) -> Result<&mut Self, ArithmeticError> {
			*self = self.ensure_mul(v)?;
			Ok(self)
		}
	}

	/// Performs self division that returns `ArithmeticError` instead of wrapping around on
	/// overflow.
	pub trait EnsureDivAssign: EnsureDiv {
		/// Divides two numbers overwriting the left hand one, checking for overflow.
		/// If overflow happens, `ArithmeticError` is returned.
		///
		/// ```
		/// use sp_runtime::traits::ensure::EnsureDivAssign;
		/// use sp_runtime::{DispatchResult, ArithmeticError, DispatchError, FixedI64};
		///
		/// fn extrinsic_zero() -> DispatchResult {
		///     let mut one = 1;
		///     one.ensure_div_assign(0)?;
		///     Ok(())
		/// }
		///
		/// fn extrinsic_overflow() -> DispatchResult {
		///     let mut min = FixedI64::from(i64::MIN);
		///     min.ensure_div_assign(FixedI64::from(-1))?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(extrinsic_zero(), Err(ArithmeticError::DivisionByZero.into()));
		/// assert_eq!(extrinsic_overflow(), Err(ArithmeticError::Overflow.into()));
		/// ```
		fn ensure_div_assign(&mut self, v: Self) -> Result<&mut Self, ArithmeticError> {
			*self = self.ensure_div(v)?;
			Ok(self)
		}
	}

	impl<T: EnsureAdd> EnsureAddAssign for T {}
	impl<T: EnsureSub> EnsureSubAssign for T {}
	impl<T: EnsureMul> EnsureMulAssign for T {}
	impl<T: EnsureDiv> EnsureDivAssign for T {}

	/// Meta trait that supports all assigned arithmetic operations
	pub trait EnsureOpAssign:
		EnsureAddAssign + EnsureSubAssign + EnsureMulAssign + EnsureDivAssign
	{
	}
	impl<T: EnsureAddAssign + EnsureSubAssign + EnsureMulAssign + EnsureDivAssign> EnsureOpAssign
		for T
	{
	}

	/// Extends `FixedPointNumber with` the Ensure family functions.
	pub trait EnsureFixedPointNumber: FixedPointNumber {
		/// Creates `self` from a rational number. Equal to `n / d`.
		///
		/// Returns `ArithmeticError` if `d == 0` or `n / d` exceeds accuracy.
		///
		/// Similar to [`FixedPointNumber::checked_from_rational()`] but returning an
		/// `ArithmeticError` error
		///
		/// ```
		/// use sp_runtime::traits::ensure::EnsureFixedPointNumber;
		/// use sp_runtime::{DispatchResult, ArithmeticError, DispatchError, FixedI64};
		///
		/// fn extrinsic_zero() -> DispatchResult {
		///     FixedI64::ensure_from_rational(1, 0)?;
		///     Ok(())
		/// }
		///
		/// fn extrinsic_underflow() -> DispatchResult {
		///     FixedI64::ensure_from_rational(i64::MAX, -1)?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(extrinsic_zero(), Err(ArithmeticError::DivisionByZero.into()));
		/// assert_eq!(extrinsic_underflow(), Err(ArithmeticError::Underflow.into()));
		/// ```
		fn ensure_from_rational<N: FixedPointOperand, D: FixedPointOperand>(
			n: N,
			d: D,
		) -> Result<Self, ArithmeticError> {
			<Self as FixedPointNumber>::checked_from_rational(n, d)
				.ok_or_else(|| error::division(n, d))
		}

		/// Ensure multiplication for integer type `N`. Equal to `self * n`.
		///
		/// Returns `ArithmeticError` if the result does not fit in `N`.
		///
		/// Similar to [`FixedPointNumber::checked_mul_int()`] but returning an ArithmeticError
		/// error
		///
		/// ```
		/// use sp_runtime::traits::ensure::EnsureFixedPointNumber;
		/// use sp_runtime::{DispatchResult, ArithmeticError, DispatchError, FixedI64};
		///
		/// fn extrinsic_overflow() -> DispatchResult {
		///     FixedI64::from(i64::MAX).ensure_mul_int(2)?;
		///     Ok(())
		/// }
		///
		/// fn extrinsic_underflow() -> DispatchResult {
		///     FixedI64::from(i64::MAX).ensure_mul_int(-2)?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(extrinsic_overflow(), Err(ArithmeticError::Overflow.into()));
		/// assert_eq!(extrinsic_underflow(), Err(ArithmeticError::Underflow.into()));
		/// ```
		fn ensure_mul_int<N: FixedPointOperand>(self, n: N) -> Result<N, ArithmeticError> {
			self.checked_mul_int(n).ok_or_else(|| error::multiplication(self, n))
		}

		/// Ensure division for integer type `N`. Equal to `self / d`.
		///
		/// Returns `ArithmeticError` if the result does not fit in `N` or `d == 0`.
		///
		/// Similar to [`FixedPointNumber::checked_div_int()`] but returning an `ArithmeticError`
		/// error
		///
		/// ```
		/// use sp_runtime::traits::ensure::EnsureFixedPointNumber;
		/// use sp_runtime::{DispatchResult, ArithmeticError, DispatchError, FixedI64};
		///
		/// fn extrinsic_zero() -> DispatchResult {
		///     FixedI64::from(1).ensure_div_int(0)?;
		///     Ok(())
		/// }
		///
		/// fn extrinsic_overflow() -> DispatchResult {
		///     FixedI64::from(i64::MIN).ensure_div_int(-1)?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(extrinsic_zero(), Err(ArithmeticError::DivisionByZero.into()));
		/// assert_eq!(extrinsic_overflow(), Err(ArithmeticError::Overflow.into()));
		/// ```
		fn ensure_div_int<D: FixedPointOperand>(self, d: D) -> Result<D, ArithmeticError> {
			self.checked_div_int(d).ok_or_else(|| error::division(self, d))
		}
	}

	impl<T: FixedPointNumber> EnsureFixedPointNumber for T {}

	/// Similar to [`TryFrom`] but returning an `ArithmeticError` error.
	pub trait EnsureFrom<T: PartialOrd + Zero + Copy>:
		TryFrom<T> + PartialOrd + Zero + Copy
	{
		/// Performs the conversion returning an `ArithmeticError` if fails.
		///
		/// Similar to [`TryFrom::try_from()`] but returning an `ArithmeticError` error
		///
		/// ```
		/// use sp_runtime::traits::ensure::EnsureFrom;
		/// use sp_runtime::{DispatchResult, ArithmeticError, DispatchError};
		///
		/// fn extrinsic_overflow() -> DispatchResult {
		///     let byte: u8 = u8::ensure_from(256u16)?;
		///     Ok(())
		/// }
		///
		/// fn extrinsic_underflow() -> DispatchResult {
		///     let byte: i8 = i8::ensure_from(-129i16)?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(extrinsic_overflow(), Err(ArithmeticError::Overflow.into()));
		/// assert_eq!(extrinsic_underflow(), Err(ArithmeticError::Underflow.into()));
		/// ```
		fn ensure_from(other: T) -> Result<Self, ArithmeticError> {
			Self::try_from(other).map_err(|_| error::equivalent(other))
		}
	}

	/// Similar to [`TryInto`] but returning an `ArithmeticError` error.
	pub trait EnsureInto<T: PartialOrd + Zero + Copy>:
		TryInto<T> + PartialOrd + Zero + Copy
	{
		/// Performs the conversion returning an `ArithmeticError` if fails.
		///
		/// Similar to [`TryInto::try_into()`] but returning an `ArithmeticError` error
		///
		/// ```
		/// use sp_runtime::traits::ensure::EnsureInto;
		/// use sp_runtime::{DispatchResult, ArithmeticError, DispatchError};
		///
		/// fn extrinsic_overflow() -> DispatchResult {
		///     let byte: u8 = 256u16.ensure_into()?;
		///     Ok(())
		/// }
		///
		/// fn extrinsic_underflow() -> DispatchResult {
		///     let byte: i8 = (-129i16).ensure_into()?;
		///     Ok(())
		/// }
		///
		/// assert_eq!(extrinsic_overflow(), Err(ArithmeticError::Overflow.into()));
		/// assert_eq!(extrinsic_underflow(), Err(ArithmeticError::Underflow.into()));
		/// ```
		fn ensure_into(self) -> Result<T, ArithmeticError> {
			self.try_into().map_err(|_| error::equivalent(self))
		}
	}

	impl<T: TryFrom<S> + PartialOrd + Zero + Copy, S: PartialOrd + Zero + Copy> EnsureFrom<S> for T {}
	impl<T: TryInto<S> + PartialOrd + Zero + Copy, S: PartialOrd + Zero + Copy> EnsureInto<S> for T {}

	mod error {
		use super::{ArithmeticError, Zero};

		#[derive(PartialEq)]
		enum Signum {
			Negative,
			Positive,
		}

		impl<T: PartialOrd + Zero> From<T> for Signum {
			fn from(value: T) -> Self {
				if value < Zero::zero() {
					Signum::Negative
				} else {
					Signum::Positive
				}
			}
		}

		impl sp_std::ops::Mul for Signum {
			type Output = Self;

			fn mul(self, rhs: Self) -> Self {
				if self != rhs {
					Signum::Negative
				} else {
					Signum::Positive
				}
			}
		}

		pub fn equivalent<R: PartialOrd + Zero + Copy>(r: R) -> ArithmeticError {
			match Signum::from(r) {
				Signum::Negative => ArithmeticError::Underflow,
				Signum::Positive => ArithmeticError::Overflow,
			}
		}

		pub fn inverse<R: PartialOrd + Zero + Copy>(r: R) -> ArithmeticError {
			match Signum::from(r) {
				Signum::Negative => ArithmeticError::Overflow,
				Signum::Positive => ArithmeticError::Underflow,
			}
		}

		pub fn multiplication<L: PartialOrd + Zero + Copy, R: PartialOrd + Zero + Copy>(
			l: L,
			r: R,
		) -> ArithmeticError {
			match Signum::from(l) * Signum::from(r) {
				Signum::Negative => ArithmeticError::Underflow,
				Signum::Positive => ArithmeticError::Overflow,
			}
		}

		pub fn division<N: PartialOrd + Zero + Copy, D: PartialOrd + Zero + Copy>(
			n: N,
			d: D,
		) -> ArithmeticError {
			if d.is_zero() {
				ArithmeticError::DivisionByZero
			} else {
				multiplication(n, d)
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::codec::{Decode, Encode, Input};
	use sp_core::{
		crypto::{Pair, UncheckedFrom},
		ecdsa,
	};

	mod t {
		use sp_application_crypto::{app_crypto, sr25519};
		use sp_core::crypto::KeyTypeId;
		app_crypto!(sr25519, KeyTypeId(*b"test"));
	}

	#[test]
	fn app_verify_works() {
		use super::AppVerify;
		use t::*;

		let s = Signature::try_from(vec![0; 64]).unwrap();
		let _ = s.verify(&[0u8; 100][..], &Public::unchecked_from([0; 32]));
	}

	#[derive(Encode, Decode, Default, PartialEq, Debug)]
	struct U128Value(u128);
	impl super::TypeId for U128Value {
		const TYPE_ID: [u8; 4] = [0x0d, 0xf0, 0x0d, 0xf0];
	}
	// f00df00d

	#[derive(Encode, Decode, Default, PartialEq, Debug)]
	struct U32Value(u32);
	impl super::TypeId for U32Value {
		const TYPE_ID: [u8; 4] = [0x0d, 0xf0, 0xfe, 0xca];
	}
	// cafef00d

	#[derive(Encode, Decode, Default, PartialEq, Debug)]
	struct U16Value(u16);
	impl super::TypeId for U16Value {
		const TYPE_ID: [u8; 4] = [0xfe, 0xca, 0x0d, 0xf0];
	}
	// f00dcafe

	type AccountId = u64;

	#[test]
	fn into_account_truncating_should_work() {
		let r: AccountId = U32Value::into_account_truncating(&U32Value(0xdeadbeef));
		assert_eq!(r, 0x_deadbeef_cafef00d);
	}

	#[test]
	fn try_into_account_should_work() {
		let r: AccountId = U32Value::try_into_account(&U32Value(0xdeadbeef)).unwrap();
		assert_eq!(r, 0x_deadbeef_cafef00d);

		// u128 is bigger than u64 would fit
		let maybe: Option<AccountId> = U128Value::try_into_account(&U128Value(u128::MAX));
		assert!(maybe.is_none());
	}

	#[test]
	fn try_from_account_should_work() {
		let r = U32Value::try_from_account(&0x_deadbeef_cafef00d_u64);
		assert_eq!(r.unwrap(), U32Value(0xdeadbeef));
	}

	#[test]
	fn into_account_truncating_with_fill_should_work() {
		let r: AccountId = U16Value::into_account_truncating(&U16Value(0xc0da));
		assert_eq!(r, 0x_0000_c0da_f00dcafe);
	}

	#[test]
	fn try_into_sub_account_should_work() {
		let r: AccountId = U16Value::try_into_account(&U16Value(0xc0da)).unwrap();
		assert_eq!(r, 0x_0000_c0da_f00dcafe);

		let maybe: Option<AccountId> = U16Value::try_into_sub_account(
			&U16Value(0xc0da),
			"a really large amount of additional encoded information which will certainly overflow the account id type ;)"
		);

		assert!(maybe.is_none())
	}

	#[test]
	fn try_from_account_with_fill_should_work() {
		let r = U16Value::try_from_account(&0x0000_c0da_f00dcafe_u64);
		assert_eq!(r.unwrap(), U16Value(0xc0da));
	}

	#[test]
	fn bad_try_from_account_should_fail() {
		let r = U16Value::try_from_account(&0x0000_c0de_baadcafe_u64);
		assert!(r.is_none());
		let r = U16Value::try_from_account(&0x0100_c0da_f00dcafe_u64);
		assert!(r.is_none());
	}

	#[test]
	fn trailing_zero_should_work() {
		let mut t = super::TrailingZeroInput(&[1, 2, 3]);
		assert_eq!(t.remaining_len(), Ok(None));
		let mut buffer = [0u8; 2];
		assert_eq!(t.read(&mut buffer), Ok(()));
		assert_eq!(t.remaining_len(), Ok(None));
		assert_eq!(buffer, [1, 2]);
		assert_eq!(t.read(&mut buffer), Ok(()));
		assert_eq!(t.remaining_len(), Ok(None));
		assert_eq!(buffer, [3, 0]);
		assert_eq!(t.read(&mut buffer), Ok(()));
		assert_eq!(t.remaining_len(), Ok(None));
		assert_eq!(buffer, [0, 0]);
	}

	#[test]
	fn ecdsa_verify_works() {
		let msg = &b"test-message"[..];
		let (pair, _) = ecdsa::Pair::generate();

		let signature = pair.sign(&msg);
		assert!(ecdsa::Pair::verify(&signature, msg, &pair.public()));

		assert!(signature.verify(msg, &pair.public()));
		assert!(signature.verify(msg, &pair.public()));
	}
}
