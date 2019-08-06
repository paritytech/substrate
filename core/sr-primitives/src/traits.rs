// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Primitives for the runtime modules.

use rstd::prelude::*;
use rstd::{self, result, marker::PhantomData, convert::{TryFrom, TryInto}};
use runtime_io;
#[cfg(feature = "std")] use std::fmt::{Debug, Display};
#[cfg(feature = "std")] use serde::{Serialize, Deserialize, de::DeserializeOwned};
use primitives::{self, Hasher, Blake2Hasher};
use crate::codec::{Codec, Encode, Decode, HasCompact};
use crate::transaction_validity::{ValidTransaction, TransactionValidity};
use crate::generic::{Digest, DigestItem};
use crate::weights::DispatchInfo;
pub use integer_sqrt::IntegerSquareRoot;
pub use num_traits::{
	Zero, One, Bounded, CheckedAdd, CheckedSub, CheckedMul, CheckedDiv,
	CheckedShl, CheckedShr
};
use rstd::ops::{
	Add, Sub, Mul, Div, Rem, AddAssign, SubAssign, MulAssign, DivAssign,
	RemAssign, Shl, Shr
};
use crate::AppKey;

/// A lazy value.
pub trait Lazy<T: ?Sized> {
	/// Get a reference to the underlying value.
	///
	/// This will compute the value if the function is invoked for the first time.
	fn get(&mut self) -> &T;
}

impl<'a> Lazy<[u8]> for &'a [u8] {
	fn get(&mut self) -> &[u8] { &**self }
}

/// Means of signature verification.
pub trait Verify {
	/// Type of the signer.
	type Signer;
	/// Verify a signature. Return `true` if signature is valid for the value.
	fn verify<L: Lazy<[u8]>>(&self, msg: L, signer: &Self::Signer) -> bool;
}

impl Verify for primitives::ed25519::Signature {
	type Signer = primitives::ed25519::Public;
	fn verify<L: Lazy<[u8]>>(&self, mut msg: L, signer: &Self::Signer) -> bool {
		runtime_io::ed25519_verify(self, msg.get(), signer)
	}
}

impl Verify for primitives::sr25519::Signature {
	type Signer = primitives::sr25519::Public;
	fn verify<L: Lazy<[u8]>>(&self, mut msg: L, signer: &Self::Signer) -> bool {
		runtime_io::sr25519_verify(self, msg.get(), signer)
	}
}

/// Means of signature verification of an application key.
pub trait AppVerify {
	/// Type of the signer.
	type Signer;
	/// Verify a signature. Return `true` if signature is valid for the value.
	fn verify<L: Lazy<[u8]>>(&self, msg: L, signer: &Self::Signer) -> bool;
}

impl<
	S: Verify<Signer=<<T as AppKey>::Public as app_crypto::AppPublic>::Generic> + From<T>,
	T: app_crypto::Wraps<Inner=S> + app_crypto::AppKey + app_crypto::AppSignature +
		AsRef<S> + AsMut<S> + From<S>,
> AppVerify for T {
	type Signer = <T as AppKey>::Public;
	fn verify<L: Lazy<[u8]>>(&self, msg: L, signer: &Self::Signer) -> bool {
		use app_crypto::IsWrappedBy;
		let inner: &S = self.as_ref();
		let inner_pubkey = <Self::Signer as app_crypto::AppPublic>::Generic::from_ref(&signer);
		Verify::verify(inner, msg, inner_pubkey)
	}
}

/// Some sort of check on the origin is performed by this object.
pub trait EnsureOrigin<OuterOrigin> {
	/// A return type.
	type Success;
	/// Perform the origin check.
	fn ensure_origin(o: OuterOrigin) -> result::Result<Self::Success, &'static str> {
		Self::try_origin(o).map_err(|_| "Invalid origin")
	}
	/// Perform the origin check.
	fn try_origin(o: OuterOrigin) -> result::Result<Self::Success, OuterOrigin>;
}

/// Means of changing one type into another in a manner dependent on the source type.
pub trait Lookup {
	/// Type to lookup from.
	type Source;
	/// Type to lookup into.
	type Target;
	/// Attempt a lookup.
	fn lookup(&self, s: Self::Source) -> result::Result<Self::Target, &'static str>;
}

/// Means of changing one type into another in a manner dependent on the source type.
/// This variant is different to `Lookup` in that it doesn't (can cannot) require any
/// context.
pub trait StaticLookup {
	/// Type to lookup from.
	type Source: Codec + Clone + PartialEq + MaybeDebug;
	/// Type to lookup into.
	type Target;
	/// Attempt a lookup.
	fn lookup(s: Self::Source) -> result::Result<Self::Target, &'static str>;
	/// Convert from Target back to Source.
	fn unlookup(t: Self::Target) -> Self::Source;
}

/// A lookup implementation returning the input value.
#[derive(Default)]
pub struct IdentityLookup<T>(PhantomData<T>);
impl<T: Codec + Clone + PartialEq + MaybeDebug> StaticLookup for IdentityLookup<T> {
	type Source = T;
	type Target = T;
	fn lookup(x: T) -> result::Result<T, &'static str> { Ok(x) }
	fn unlookup(x: T) -> T { x }
}
impl<T> Lookup for IdentityLookup<T> {
	type Source = T;
	type Target = T;
	fn lookup(&self, x: T) -> result::Result<T, &'static str> { Ok(x) }
}

/// Extensible conversion trait. Generic over both source and destination types.
pub trait Convert<A, B> {
	/// Make conversion.
	fn convert(a: A) -> B;
}

impl<A, B: Default> Convert<A, B> for () {
	fn convert(_: A) -> B { Default::default() }
}

/// A structure that performs identity conversion.
pub struct Identity;
impl<T> Convert<T, T> for Identity {
	fn convert(a: T) -> T { a }
}

/// A structure that performs standard conversion using the standard Rust conversion traits.
pub struct ConvertInto;
impl<A, B: From<A>> Convert<A, B> for ConvertInto {
	fn convert(a: A) -> B { a.into() }
}

/// A meta trait for arithmetic.
///
/// Arithmetic types do all the usual stuff you'd expect numbers to do. They are guaranteed to
/// be able to represent at least `u32` values without loss, hence the trait implies `From<u32>`
/// and smaller ints. All other conversions are fallible.
pub trait SimpleArithmetic:
	Zero + One + IntegerSquareRoot +
	From<u8> + From<u16> + From<u32> + TryInto<u8> + TryInto<u16> + TryInto<u32> +
	TryFrom<u64> + TryInto<u64> + TryFrom<u128> + TryInto<u128> + TryFrom<usize> + TryInto<usize> +
	UniqueSaturatedInto<u8> + UniqueSaturatedInto<u16> + UniqueSaturatedInto<u32> +
	UniqueSaturatedFrom<u64> + UniqueSaturatedInto<u64> + UniqueSaturatedFrom<u128> + UniqueSaturatedInto<u128> +
	Add<Self, Output = Self> + AddAssign<Self> +
	Sub<Self, Output = Self> + SubAssign<Self> +
	Mul<Self, Output = Self> + MulAssign<Self> +
	Div<Self, Output = Self> + DivAssign<Self> +
	Rem<Self, Output = Self> + RemAssign<Self> +
	Shl<u32, Output = Self> + Shr<u32, Output = Self> +
	CheckedShl + CheckedShr + CheckedAdd + CheckedSub + CheckedMul + CheckedDiv +
	Saturating + PartialOrd<Self> + Ord + Bounded +
	HasCompact + Sized
{}
impl<T:
	Zero + One + IntegerSquareRoot +
	From<u8> + From<u16> + From<u32> + TryInto<u8> + TryInto<u16> + TryInto<u32> +
	TryFrom<u64> + TryInto<u64> + TryFrom<u128> + TryInto<u128> + TryFrom<usize> + TryInto<usize> +
	UniqueSaturatedInto<u8> + UniqueSaturatedInto<u16> + UniqueSaturatedInto<u32> +
	UniqueSaturatedFrom<u64> + UniqueSaturatedInto<u64> + UniqueSaturatedFrom<u128> +
	UniqueSaturatedInto<u128> + UniqueSaturatedFrom<usize> + UniqueSaturatedInto<usize> +
	Add<Self, Output = Self> + AddAssign<Self> +
	Sub<Self, Output = Self> + SubAssign<Self> +
	Mul<Self, Output = Self> + MulAssign<Self> +
	Div<Self, Output = Self> + DivAssign<Self> +
	Rem<Self, Output = Self> + RemAssign<Self> +
	Shl<u32, Output = Self> + Shr<u32, Output = Self> +
	CheckedShl + CheckedShr + CheckedAdd + CheckedSub + CheckedMul + CheckedDiv +
	Saturating + PartialOrd<Self> + Ord + Bounded +
	HasCompact + Sized
> SimpleArithmetic for T {}

/// Just like `From` except that if the source value is too big to fit into the destination type
/// then it'll saturate the destination.
pub trait UniqueSaturatedFrom<T: Sized>: Sized {
	/// Convert from a value of `T` into an equivalent instance of `Self`.
	fn unique_saturated_from(t: T) -> Self;
}

/// Just like `Into` except that if the source value is too big to fit into the destination type
/// then it'll saturate the destination.
pub trait UniqueSaturatedInto<T: Sized>: Sized {
	/// Consume self to return an equivalent value of `T`.
	fn unique_saturated_into(self) -> T;
}

impl<T: Sized, S: TryFrom<T> + Bounded + Sized> UniqueSaturatedFrom<T> for S {
	fn unique_saturated_from(t: T) -> Self {
		S::try_from(t).unwrap_or_else(|_| Bounded::max_value())
	}
}

impl<T: Bounded + Sized, S: TryInto<T> + Sized> UniqueSaturatedInto<T> for S {
	fn unique_saturated_into(self) -> T {
		self.try_into().unwrap_or_else(|_| Bounded::max_value())
	}
}

/// Simple trait to use checked mul and max value to give a saturated mul operation over
/// supported types.
pub trait Saturating {
	/// Saturated addition - if the product can't fit in the type then just use max-value.
	fn saturating_add(self, o: Self) -> Self;

	/// Saturated subtraction - if the product can't fit in the type then just use max-value.
	fn saturating_sub(self, o: Self) -> Self;

	/// Saturated multiply - if the product can't fit in the type then just use max-value.
	fn saturating_mul(self, o: Self) -> Self;
}

impl<T: CheckedMul + Bounded + num_traits::Saturating> Saturating for T {
	fn saturating_add(self, o: Self) -> Self {
		<Self as num_traits::Saturating>::saturating_add(self, o)
	}
	fn saturating_sub(self, o: Self) -> Self {
		<Self as num_traits::Saturating>::saturating_sub(self, o)
	}
	fn saturating_mul(self, o: Self) -> Self {
		self.checked_mul(&o).unwrap_or_else(Bounded::max_value)
	}
}

/// Convenience type to work around the highly unergonomic syntax needed
/// to invoke the functions of overloaded generic traits, in this case
/// `SaturatedFrom` and `SaturatedInto`.
pub trait SaturatedConversion {
	/// Convert from a value of `T` into an equivalent instance of `Self`.
	///
	/// This just uses `UniqueSaturatedFrom` internally but with this
	/// variant you can provide the destination type using turbofish syntax
	/// in case Rust happens not to assume the correct type.
	fn saturated_from<T>(t: T) -> Self where Self: UniqueSaturatedFrom<T> {
		<Self as UniqueSaturatedFrom<T>>::unique_saturated_from(t)
	}

	/// Consume self to return an equivalent value of `T`.
	///
	/// This just uses `UniqueSaturatedInto` internally but with this
	/// variant you can provide the destination type using turbofish syntax
	/// in case Rust happens not to assume the correct type.
	fn saturated_into<T>(self) -> T where Self: UniqueSaturatedInto<T> {
		<Self as UniqueSaturatedInto<T>>::unique_saturated_into(self)
	}
}
impl<T: Sized> SaturatedConversion for T {}

/// Convenience type to work around the highly unergonomic syntax needed
/// to invoke the functions of overloaded generic traits, in this case
/// `TryFrom` and `TryInto`.
pub trait CheckedConversion {
	/// Convert from a value of `T` into an equivalent instance of `Option<Self>`.
	///
	/// This just uses `TryFrom` internally but with this
	/// variant you can provide the destination type using turbofish syntax
	/// in case Rust happens not to assume the correct type.
	fn checked_from<T>(t: T) -> Option<Self> where Self: TryFrom<T> {
		<Self as TryFrom<T>>::try_from(t).ok()
	}
	/// Consume self to return `Some` equivalent value of `Option<T>`.
	///
	/// This just uses `TryInto` internally but with this
	/// variant you can provide the destination type using turbofish syntax
	/// in case Rust happens not to assume the correct type.
	fn checked_into<T>(self) -> Option<T> where Self: TryInto<T> {
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
			fn mul(self, other: $other) -> Self::Output { self * (other as Self) }
			fn div(self, other: $other) -> Self::Output { self / (other as Self) }
			fn rem(self, other: $other) -> Self::Output { self % (other as Self) }
		}
	}
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
	fn is_clear(&self) -> bool { *self == Self::clear() }
	fn clear() -> Self { Default::default() }
}

/// A meta trait for all bit ops.
pub trait SimpleBitOps:
	Sized + Clear +
	rstd::ops::BitOr<Self, Output = Self> +
	rstd::ops::BitXor<Self, Output = Self> +
	rstd::ops::BitAnd<Self, Output = Self>
{}
impl<T:
	Sized + Clear +
	rstd::ops::BitOr<Self, Output = Self> +
	rstd::ops::BitXor<Self, Output = Self> +
	rstd::ops::BitAnd<Self, Output = Self>
> SimpleBitOps for T {}

/// The block finalization trait. Implementing this lets you express what should happen
/// for your module when the block is ending.
pub trait OnFinalize<BlockNumber> {
	/// The block is being finalized. Implement to have something happen.
	fn on_finalize(_n: BlockNumber) {}
}

impl<N> OnFinalize<N> for () {}

/// The block initialization trait. Implementing this lets you express what should happen
/// for your module when the block is beginning (right before the first extrinsic is executed).
pub trait OnInitialize<BlockNumber> {
	/// The block is being initialized. Implement to have something happen.
	fn on_initialize(_n: BlockNumber) {}
}

impl<N> OnInitialize<N> for () {}

/// Off-chain computation trait.
///
/// Implementing this trait on a module allows you to perform long-running tasks
/// that make validators generate extrinsics (either transactions or inherents)
/// with the results of those long-running computations.
///
/// NOTE: This function runs off-chain, so it can access the block state,
/// but cannot preform any alterations.
pub trait OffchainWorker<BlockNumber> {
	/// This function is being called on every block.
	///
	/// Implement this and use special `extern`s to generate transactions or inherents.
	/// Any state alterations are lost and are not persisted.
	fn generate_extrinsics(_n: BlockNumber) {}
}

impl<N> OffchainWorker<N> for () {}

macro_rules! tuple_impl {
	($first:ident, $($rest:ident,)+) => {
		tuple_impl!([$first] [$first] [$($rest)+]);
	};
	([$($direct:ident)+] [$($reverse:ident)+] []) => {
		impl<
			Number: Copy,
			$($direct: OnFinalize<Number>),+
		> OnFinalize<Number> for ($($direct),+,) {
			fn on_finalize(n: Number) {
				$($reverse::on_finalize(n);)+
			}
		}
		impl<
			Number: Copy,
			$($direct: OnInitialize<Number>),+
		> OnInitialize<Number> for ($($direct),+,) {
			fn on_initialize(n: Number) {
				$($direct::on_initialize(n);)+
			}
		}
		impl<
			Number: Copy,
			$($direct: OffchainWorker<Number>),+
		> OffchainWorker<Number> for ($($direct),+,) {
			fn generate_extrinsics(n: Number) {
				$($direct::generate_extrinsics(n);)+
			}
		}
	};
	([$($direct:ident)+] [$($reverse:ident)+] [$first:ident $($rest:ident)*]) => {
		tuple_impl!([$($direct)+] [$($reverse)+] []);
		tuple_impl!([$($direct)+ $first] [$first $($reverse)+] [$($rest)*]);
	};
}

#[allow(non_snake_case)]
tuple_impl!(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z,);

/// Abstraction around hashing
pub trait Hash: 'static + MaybeSerializeDebug + Clone + Eq + PartialEq {	// Stupid bug in the Rust compiler believes derived
																	// traits must be fulfilled by all type parameters.
	/// The hash type produced.
	type Output: Member + MaybeSerializeDebug + rstd::hash::Hash + AsRef<[u8]> + AsMut<[u8]> + Copy
		+ Default + Encode + Decode;

	/// The associated hash_db Hasher type.
	type Hasher: Hasher<Out=Self::Output>;

	/// Produce the hash of some byte-slice.
	fn hash(s: &[u8]) -> Self::Output;

	/// Produce the hash of some codec-encodable value.
	fn hash_of<S: Encode>(s: &S) -> Self::Output {
		Encode::using_encoded(s, Self::hash)
	}

	/// Iterator-based version of `ordered_trie_root`.
	fn ordered_trie_root<
		I: IntoIterator<Item = A>,
		A: AsRef<[u8]>
	>(input: I) -> Self::Output;

	/// The Patricia tree root of the given mapping as an iterator.
	fn trie_root<
		I: IntoIterator<Item = (A, B)>,
		A: AsRef<[u8]> + Ord,
		B: AsRef<[u8]>
	>(input: I) -> Self::Output;

	/// Acquire the global storage root.
	fn storage_root() -> Self::Output;

	/// Acquire the global storage changes root.
	fn storage_changes_root(parent_hash: Self::Output) -> Option<Self::Output>;
}

/// Blake2-256 Hash implementation.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct BlakeTwo256;

impl Hash for BlakeTwo256 {
	type Output = primitives::H256;
	type Hasher = Blake2Hasher;
	fn hash(s: &[u8]) -> Self::Output {
		runtime_io::blake2_256(s).into()
	}
	fn trie_root<
		I: IntoIterator<Item = (A, B)>,
		A: AsRef<[u8]> + Ord,
		B: AsRef<[u8]>
	>(input: I) -> Self::Output {
		runtime_io::trie_root::<Blake2Hasher, _, _, _>(input).into()
	}
	fn ordered_trie_root<
		I: IntoIterator<Item = A>,
		A: AsRef<[u8]>
	>(input: I) -> Self::Output {
		runtime_io::ordered_trie_root::<Blake2Hasher, _, _>(input).into()
	}
	fn storage_root() -> Self::Output {
		runtime_io::storage_root().into()
	}
	fn storage_changes_root(parent_hash: Self::Output) -> Option<Self::Output> {
		runtime_io::storage_changes_root(parent_hash.into()).map(Into::into)
	}
}

/// Something that can be checked for equality and printed out to a debug channel if bad.
pub trait CheckEqual {
	/// Perform the equality check.
	fn check_equal(&self, other: &Self);
}

impl CheckEqual for primitives::H256 {
	#[cfg(feature = "std")]
	fn check_equal(&self, other: &Self) {
		use primitives::hexdisplay::HexDisplay;
		if self != other {
			println!("Hash: given={}, expected={}", HexDisplay::from(self.as_fixed_bytes()), HexDisplay::from(other.as_fixed_bytes()));
		}
	}

	#[cfg(not(feature = "std"))]
	fn check_equal(&self, other: &Self) {
		if self != other {
			runtime_io::print("Hash not equal");
			runtime_io::print(self.as_bytes());
			runtime_io::print(other.as_bytes());
		}
	}
}

impl<H: PartialEq + Eq + MaybeDebug> CheckEqual for super::generic::DigestItem<H> where H: Encode {
	#[cfg(feature = "std")]
	fn check_equal(&self, other: &Self) {
		if self != other {
			println!("DigestItem: given={:?}, expected={:?}", self, other);
		}
	}

	#[cfg(not(feature = "std"))]
	fn check_equal(&self, other: &Self) {
		if self != other {
			runtime_io::print("DigestItem not equal");
			runtime_io::print(&Encode::encode(self)[..]);
			runtime_io::print(&Encode::encode(other)[..]);
		}
	}
}

/// A type that implements Serialize and Debug when in std environment.
#[cfg(feature = "std")]
pub trait MaybeSerializeDebugButNotDeserialize: Serialize + Debug {}
#[cfg(feature = "std")]
impl<T: Serialize + Debug> MaybeSerializeDebugButNotDeserialize for T {}

/// A type that implements Serialize and Debug when in std environment.
#[cfg(not(feature = "std"))]
pub trait MaybeSerializeDebugButNotDeserialize {}
#[cfg(not(feature = "std"))]
impl<T> MaybeSerializeDebugButNotDeserialize for T {}

/// A type that implements Serialize when in std environment.
#[cfg(feature = "std")]
pub trait MaybeSerialize: Serialize {}
#[cfg(feature = "std")]
impl<T: Serialize> MaybeSerialize for T {}

/// A type that implements Serialize when in std environment.
#[cfg(not(feature = "std"))]
pub trait MaybeSerialize {}
#[cfg(not(feature = "std"))]
impl<T> MaybeSerialize for T {}

/// A type that implements Serialize, DeserializeOwned and Debug when in std environment.
#[cfg(feature = "std")]
pub trait MaybeSerializeDebug: Serialize + DeserializeOwned + Debug {}
#[cfg(feature = "std")]
impl<T: Serialize + DeserializeOwned + Debug> MaybeSerializeDebug for T {}

/// A type that implements Serialize, DeserializeOwned and Debug when in std environment.
#[cfg(not(feature = "std"))]
pub trait MaybeSerializeDebug {}
#[cfg(not(feature = "std"))]
impl<T> MaybeSerializeDebug for T {}

/// A type that implements Debug when in std environment.
#[cfg(feature = "std")]
pub trait MaybeDebug: Debug {}
#[cfg(feature = "std")]
impl<T: Debug> MaybeDebug for T {}

/// A type that implements Debug when in std environment.
#[cfg(not(feature = "std"))]
pub trait MaybeDebug {}
#[cfg(not(feature = "std"))]
impl<T> MaybeDebug for T {}

/// A type that implements Display when in std environment.
#[cfg(feature = "std")]
pub trait MaybeDisplay: Display {}
#[cfg(feature = "std")]
impl<T: Display> MaybeDisplay for T {}

/// A type that implements Display when in std environment.
#[cfg(not(feature = "std"))]
pub trait MaybeDisplay {}
#[cfg(not(feature = "std"))]
impl<T> MaybeDisplay for T {}

/// A type that implements Hash when in std environment.
#[cfg(feature = "std")]
pub trait MaybeHash: ::rstd::hash::Hash {}
#[cfg(feature = "std")]
impl<T: ::rstd::hash::Hash> MaybeHash for T {}

/// A type that implements Hash when in std environment.
#[cfg(not(feature = "std"))]
pub trait MaybeHash {}
#[cfg(not(feature = "std"))]
impl<T> MaybeHash for T {}

/// A type that provides a randomness beacon.
pub trait RandomnessBeacon {
	/// Returns 32 bytes of random data. The output will change eventually, but
	/// is not guaranteed to be different between any two calls.
	///
	/// # Security
	///
	/// This MUST NOT be used for gambling, as it can be influenced by a
	/// malicious validator in the short term.  It MAY be used in many
	/// cryptographic protocols, however, so long as one remembers that this
	/// (like everything else on-chain) is public.  For example, it can be
	/// used where a number is needed that cannot have been chosen by an
	/// adversary, for purposes such as public-coin zero-knowledge proofs.
	fn random() -> [u8; 32];
}

/// A type that can be used in runtime structures.
pub trait Member: Send + Sync + Sized + MaybeDebug + Eq + PartialEq + Clone + 'static {}
impl<T: Send + Sync + Sized + MaybeDebug + Eq + PartialEq + Clone + 'static> Member for T {}

/// Determine if a `MemberId` is a valid member.
pub trait IsMember<MemberId> {
	/// Is the given `MemberId` a valid member?
	fn is_member(member_id: &MemberId) -> bool;
}

/// Something which fulfills the abstract idea of a Substrate header. It has types for a `Number`,
/// a `Hash` and a `Digest`. It provides access to an `extrinsics_root`, `state_root` and
/// `parent_hash`, as well as a `digest` and a block `number`.
///
/// You can also create a `new` one from those fields.
pub trait Header: Clone + Send + Sync + Codec + Eq + MaybeSerializeDebugButNotDeserialize + 'static {
	/// Header number.
	type Number: Member + MaybeSerializeDebug + ::rstd::hash::Hash + Copy + MaybeDisplay + SimpleArithmetic + Codec;
	/// Header hash type
	type Hash: Member + MaybeSerializeDebug + ::rstd::hash::Hash + Copy + MaybeDisplay + Default + SimpleBitOps + Codec + AsRef<[u8]> + AsMut<[u8]>;
	/// Hashing algorithm
	type Hashing: Hash<Output = Self::Hash>;

	/// Creates new header.
	fn new(
		number: Self::Number,
		extrinsics_root: Self::Hash,
		state_root: Self::Hash,
		parent_hash: Self::Hash,
		digest: Digest<Self::Hash>,
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
	fn digest(&self) -> &Digest<Self::Hash>;
	/// Get a mutable reference to the digest.
	fn digest_mut(&mut self) -> &mut Digest<Self::Hash>;

	/// Returns the hash of the header.
	fn hash(&self) -> Self::Hash {
		<Self::Hashing as Hash>::hash_of(self)
	}
}

/// Something which fulfills the abstract idea of a Substrate block. It has types for an
/// `Extrinsic` piece of information as well as a `Header`.
///
/// You can get an iterator over each of the `extrinsics` and retrieve the `header`.
pub trait Block: Clone + Send + Sync + Codec + Eq + MaybeSerializeDebugButNotDeserialize + 'static {
	/// Type of extrinsics.
	type Extrinsic: Member + Codec + Extrinsic + MaybeSerialize;
	/// Header type.
	type Header: Header<Hash=Self::Hash>;
	/// Block hash type.
	type Hash: Member + MaybeSerializeDebug + ::rstd::hash::Hash + Copy + MaybeDisplay + Default + SimpleBitOps + Codec + AsRef<[u8]> + AsMut<[u8]>;

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
}

/// Something that acts like an `Extrinsic`.
pub trait Extrinsic: Sized {
	/// The function call.
	type Call;

	/// Is this `Extrinsic` signed?
	/// If no information are available about signed/unsigned, `None` should be returned.
	fn is_signed(&self) -> Option<bool> { None }

	/// New instance of an unsigned extrinsic aka "inherent". `None` if this is an opaque
	/// extrinsic type.
	fn new_unsigned(_call: Self::Call) -> Option<Self> { None }
}

/// Extract the hashing type for a block.
pub type HashFor<B> = <<B as Block>::Header as Header>::Hashing;
/// Extract the number type for a block.
pub type NumberFor<B> = <<B as Block>::Header as Header>::Number;
/// Extract the digest type for a block.
pub type DigestFor<B> = Digest<<<B as Block>::Header as Header>::Hash>;
/// Extract the digest item type for a block.
pub type DigestItemFor<B> = DigestItem<<<B as Block>::Header as Header>::Hash>;
/// Extract the digest item type for a header.
pub type DigestItemForHeader<H> = DigestItem<<H as Header>::Hash>;

/// A "checkable" piece of information, used by the standard Substrate Executive in order to
/// check the validity of a piece of extrinsic information, usually by verifying the signature.
/// Implement for pieces of information that require some additional context `Context` in order to be
/// checked.
pub trait Checkable<Context>: Sized {
	/// Returned if `check` succeeds.
	type Checked;

	/// Check self, given an instance of Context.
	fn check(self, c: &Context) -> Result<Self::Checked, &'static str>;
}

/// A "checkable" piece of information, used by the standard Substrate Executive in order to
/// check the validity of a piece of extrinsic information, usually by verifying the signature.
/// Implement for pieces of information that don't require additional context in order to be
/// checked.
pub trait BlindCheckable: Sized {
	/// Returned if `check` succeeds.
	type Checked;

	/// Check self.
	fn check(self) -> Result<Self::Checked, &'static str>;
}

// Every `BlindCheckable` is also a `StaticCheckable` for arbitrary `Context`.
impl<T: BlindCheckable, Context> Checkable<Context> for T {
	type Checked = <Self as BlindCheckable>::Checked;
	fn check(self, _c: &Context) -> Result<Self::Checked, &'static str> {
		BlindCheckable::check(self)
	}
}

/// An abstract error concerning an attempt to verify, check or dispatch the transaction. This
/// cannot be more concrete because it's designed to work reasonably well over a broad range of
/// possible transaction types.
#[cfg_attr(feature = "std", derive(Debug))]
pub enum DispatchError {
	/// General error to do with the inability to pay some fees (e.g. account balance too low).
	Payment,

	/// General error to do with the exhaustion of block resources.
	Exhausted,

	/// General error to do with the permissions of the sender.
	NoPermission,

	/// General error to do with the state of the system in general.
	BadState,

	/// General error to do with the transaction being outdated (e.g. nonce too low).
	Stale,

	/// General error to do with the transaction not yet being valid (e.g. nonce too high).
	Future,

	/// General error to do with the transaction's proofs (e.g. signature).
	BadProof,
}

impl From<DispatchError> for i8 {
	fn from(e: DispatchError) -> i8 {
		match e {
			DispatchError::Payment => -64,
			DispatchError::Exhausted => -65,
			DispatchError::NoPermission => -66,
			DispatchError::BadState => -67,
			DispatchError::Stale => -68,
			DispatchError::Future => -69,
			DispatchError::BadProof => -70,
		}
	}
}

/// Result of a module function call; either nothing (functions are only called for "side effects")
/// or an error message.
pub type DispatchResult = result::Result<(), &'static str>;

/// A lazy call (module function and argument values) that can be executed via its `dispatch`
/// method.
pub trait Dispatchable {
	/// Every function call from your runtime has an origin, which specifies where the extrinsic was
	/// generated from. In the case of a signed extrinsic (transaction), the origin contains an
	/// identifier for the caller. The origin can be empty in the case of an inherent extrinsic.
	type Origin;
	/// ...
	type Trait;
	/// Actually dispatch this call and result the result of it.
	fn dispatch(self, origin: Self::Origin) -> DispatchResult;
}

/// Means by which a transaction may be extended. This type embodies both the data and the logic
/// that should be additionally associated with the transaction. It should be plain old data.
pub trait SignedExtension:
	Codec + MaybeDebug + Sync + Send + Clone + Eq + PartialEq
{
	/// The type which encodes the sender identity.
	type AccountId;

	/// The type which encodes the call to be dispatched.
	type Call;

	/// Any additional data that will go into the signed payload. This may be created dynamically
	/// from the transaction using the `additional_signed` function.
	type AdditionalSigned: Encode;

	/// The type that encodes information that can be passed from pre_dispatch to post-dispatch.
	type Pre: Default;

	/// Construct any additional data that should be in the signed payload of the transaction. Can
	/// also perform any pre-signature-verification checks and return an error if needed.
	fn additional_signed(&self) -> Result<Self::AdditionalSigned, &'static str>;

	/// Validate a signed transaction for the transaction queue.
	fn validate(
		&self,
		_who: &Self::AccountId,
		_call: &Self::Call,
		_info: DispatchInfo,
		_len: usize,
	) -> Result<ValidTransaction, DispatchError> {
		Ok(Default::default())
	}

	/// Do any pre-flight stuff for a signed transaction.
	fn pre_dispatch(
		self,
		who: &Self::AccountId,
		call: &Self::Call,
		info: DispatchInfo,
		len: usize,
	) -> Result<Self::Pre, DispatchError> {
		self.validate(who, call, info, len).map(|_| Self::Pre::default())
	}

	/// Validate an unsigned transaction for the transaction queue. Normally the default
	/// implementation is fine since `ValidateUnsigned` is a better way of recognising and
	/// validating unsigned transactions.
	fn validate_unsigned(
		_call: &Self::Call,
		_info: DispatchInfo,
		_len: usize,
	) -> Result<ValidTransaction, DispatchError> { Ok(Default::default()) }

	/// Do any pre-flight stuff for a unsigned transaction.
	fn pre_dispatch_unsigned(
		call: &Self::Call,
		info: DispatchInfo,
		len: usize,
	) -> Result<Self::Pre, DispatchError> {
		Self::validate_unsigned(call, info, len).map(|_| Self::Pre::default())
	}

	/// Do any post-flight stuff for a transaction.
	fn post_dispatch(
		_pre: Self::Pre,
		_info: DispatchInfo,
		_len: usize,
	) { }
}

macro_rules! tuple_impl_indexed {
	($first:ident, $($rest:ident,)+ ; $first_index:tt, $($rest_index:tt,)+) => {
		tuple_impl_indexed!([$first] [$($rest)+] ; [$first_index,] [$($rest_index,)+]);
	};
	([$($direct:ident)+] ; [$($index:tt,)+]) => {
		impl<
			AccountId,
			Call,
			$($direct: SignedExtension<AccountId=AccountId, Call=Call>),+
		> SignedExtension for ($($direct),+,) {
			type AccountId = AccountId;
			type Call = Call;
			type AdditionalSigned = ($($direct::AdditionalSigned,)+);
			type Pre =  ($($direct::Pre,)+);
			fn additional_signed(&self) -> Result<Self::AdditionalSigned, &'static str> {
				Ok(( $(self.$index.additional_signed()?,)+ ))
			}
			fn validate(
				&self,
				who: &Self::AccountId,
				call: &Self::Call,
				info: DispatchInfo,
				len: usize,
			) -> Result<ValidTransaction, DispatchError> {
				let aggregator = vec![$(<$direct as SignedExtension>::validate(&self.$index, who, call, info, len)?),+];
				Ok(aggregator.into_iter().fold(ValidTransaction::default(), |acc, a| acc.combine_with(a)))
			}
			fn pre_dispatch(
				self,
				who: &Self::AccountId,
				call: &Self::Call,
				info: DispatchInfo,
				len: usize,
			) -> Result<Self::Pre, DispatchError> {
				Ok(($(self.$index.pre_dispatch(who, call, info, len)?,)+))
			}
			fn validate_unsigned(
				call: &Self::Call,
				info: DispatchInfo,
				len: usize,
			) -> Result<ValidTransaction, DispatchError> {
				let aggregator = vec![$($direct::validate_unsigned(call, info, len)?),+];
				Ok(aggregator.into_iter().fold(ValidTransaction::default(), |acc, a| acc.combine_with(a)))
			}
			fn pre_dispatch_unsigned(
				call: &Self::Call,
				info: DispatchInfo,
				len: usize,
			) -> Result<Self::Pre, DispatchError> {
				Ok(($($direct::pre_dispatch_unsigned(call, info, len)?,)+))
			}
			fn post_dispatch(
				pre: Self::Pre,
				info: DispatchInfo,
				len: usize,
			) {
				$($direct::post_dispatch(pre.$index, info, len);)+
			}
		}

	};
	([$($direct:ident)+] [] ; [$($index:tt,)+] []) => {
		tuple_impl_indexed!([$($direct)+] ; [$($index,)+]);
	};
	(
		[$($direct:ident)+] [$first:ident $($rest:ident)*]
		;
		[$($index:tt,)+] [$first_index:tt, $($rest_index:tt,)*]
	) => {
		tuple_impl_indexed!([$($direct)+] ; [$($index,)+]);
		tuple_impl_indexed!([$($direct)+ $first] [$($rest)*] ; [$($index,)+ $first_index,] [$($rest_index,)*]);
	};
}

// TODO: merge this into `tuple_impl` once codec supports `trait Codec` for longer tuple lengths. #3152
#[allow(non_snake_case)]
tuple_impl_indexed!(A, B, C, D, E, F, G, H, I, J, ; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,);

/// Only for bare bone testing when you don't care about signed extensions at all.
#[cfg(feature = "std")]
impl SignedExtension for () {
	type AccountId = u64;
	type AdditionalSigned = ();
	type Call = ();
	type Pre = ();
	fn additional_signed(&self) -> rstd::result::Result<(), &'static str> { Ok(()) }
}

/// An "executable" piece of information, used by the standard Substrate Executive in order to
/// enact a piece of extrinsic information by marshalling and dispatching to a named function
/// call.
///
/// Also provides information on to whom this information is attributable and an index that allows
/// each piece of attributable information to be disambiguated.
pub trait Applyable: Sized + Send + Sync {
	/// Id of the account that is responsible for this piece of information (sender).
	type AccountId: Member + MaybeDisplay;

	/// Type by which we can dispatch. Restricts the UnsignedValidator type.
	type Call;

	/// Returns a reference to the sender if any.
	fn sender(&self) -> Option<&Self::AccountId>;

	/// Checks to see if this is a valid *transaction*. It returns information on it if so.
	fn validate<V: ValidateUnsigned<Call=Self::Call>>(&self,
		info: DispatchInfo,
		len: usize,
	) -> TransactionValidity;

	/// Executes all necessary logic needed prior to dispatch and deconstructs into function call,
	/// index and sender.
	fn dispatch(self,
		info: DispatchInfo,
		len: usize,
	) -> Result<DispatchResult, DispatchError>;
}

/// Auxiliary wrapper that holds an api instance and binds it to the given lifetime.
pub struct ApiRef<'a, T>(T, rstd::marker::PhantomData<&'a ()>);

impl<'a, T> From<T> for ApiRef<'a, T> {
	fn from(api: T) -> Self {
		ApiRef(api, Default::default())
	}
}

impl<'a, T> rstd::ops::Deref for ApiRef<'a, T> {
	type Target = T;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

impl<'a, T> rstd::ops::DerefMut for ApiRef<'a, T> {
	fn deref_mut(&mut self) -> &mut T {
		&mut self.0
	}
}

/// Something that provides a runtime api.
pub trait ProvideRuntimeApi {
	/// The concrete type that provides the api.
	type Api;

	/// Returns the runtime api.
	/// The returned instance will keep track of modifications to the storage. Any successful
	/// call to an api function, will `commit` its changes to an internal buffer. Otherwise,
	/// the modifications will be `discarded`. The modifications will not be applied to the
	/// storage, even on a `commit`.
	fn runtime_api<'a>(&'a self) -> ApiRef<'a, Self::Api>;
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

/// Something that provides information about a runtime api.
pub trait RuntimeApiInfo {
	/// The identifier of the runtime api.
	const ID: [u8; 8];
	/// The version of the runtime api.
	const VERSION: u32;
}

/// Something that can validate unsigned extrinsics.
pub trait ValidateUnsigned {
	/// The call to validate
	type Call;

	/// Return the validity of the call
	///
	/// This doesn't execute any side-effects; it merely checks
	/// whether the transaction would panic if it were included or not.
	///
	/// Changes made to storage should be discarded by caller.
	fn validate_unsigned(call: &Self::Call) -> TransactionValidity;
}

/// Opaque datatype that may be destructured into a series of raw byte slices (which represent
/// individual keys).
pub trait OpaqueKeys: Clone {
	/// An iterator over the type IDs of keys that this holds.
	type KeyTypeIds: IntoIterator<Item=super::KeyTypeId>;

	/// Return an iterator over the key-type IDs supported by this set.
	fn key_ids() -> Self::KeyTypeIds;
	/// Get the raw bytes of key with key-type ID `i`.
	fn get_raw(&self, i: super::KeyTypeId) -> &[u8];
	/// Get the decoded key with index `i`.
	fn get<T: Decode>(&self, i: super::KeyTypeId) -> Option<T> {
		T::decode(&mut self.get_raw(i)).ok()
	}
	/// Verify a proof of ownership for the keys.
	fn ownership_proof_is_valid(&self, _proof: &[u8]) -> bool { true }
}

/// Input that adds infinite number of zero after wrapped input.
struct TrailingZeroInput<'a>(&'a [u8]);

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
	/// Convert into an account ID. This is infallible.
	fn into_account(&self) -> AccountId { self.into_sub_account(&()) }

	/// Try to convert an account ID into this type. Might not succeed.
	fn try_from_account(a: &AccountId) -> Option<Self> {
		Self::try_from_sub_account::<()>(a).map(|x| x.0)
	}

	/// Convert this value amalgamated with the a secondary "sub" value into an account ID. This is
	/// infallible.
	///
	/// NOTE: The account IDs from this and from `into_account` are *not* guaranteed to be distinct
	/// for any given value of `self`, nor are different invocations to this with different types
	/// `T`. For example, the following will all encode to the same account ID value:
	/// - `self.into_sub_account(0u32)`
	/// - `self.into_sub_account(vec![0u8; 0])`
	/// - `self.into_account()`
	fn into_sub_account<S: Encode>(&self, sub: S) -> AccountId;

	/// Try to convert an account ID into this type. Might not succeed.
	fn try_from_sub_account<S: Decode>(x: &AccountId) -> Option<(Self, S)>;
}

/// Provide a simple 4 byte identifier for a type.
pub trait TypeId {
	/// Simple 4 byte identifier.
	const TYPE_ID: [u8; 4];
}

/// Format is TYPE_ID ++ encode(parachain ID) ++ 00.... where 00... is indefinite trailing zeroes to
/// fill AccountId.
impl<T: Encode + Decode + Default, Id: Encode + Decode + TypeId> AccountIdConversion<T> for Id {
	fn into_sub_account<S: Encode>(&self, sub: S) -> T {
		(Id::TYPE_ID, self, sub).using_encoded(|b|
			T::decode(&mut TrailingZeroInput(b))
		).unwrap_or_default()
	}

	fn try_from_sub_account<S: Decode>(x: &T) -> Option<(Self, S)> {
		x.using_encoded(|d| {
			if &d[0..4] != Id::TYPE_ID { return None }
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

#[cfg(test)]
mod tests {
	use super::AccountIdConversion;
	use crate::codec::{Encode, Decode, Input};

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
	fn into_account_should_work() {
		let r: AccountId = U32Value::into_account(&U32Value(0xdeadbeef));
		assert_eq!(r, 0x_deadbeef_cafef00d);
	}

	#[test]
	fn try_from_account_should_work() {
		let r = U32Value::try_from_account(&0x_deadbeef_cafef00d_u64);
		assert_eq!(r.unwrap(), U32Value(0xdeadbeef));
	}

	#[test]
	fn into_account_with_fill_should_work() {
		let r: AccountId = U16Value::into_account(&U16Value(0xc0da));
		assert_eq!(r, 0x_0000_c0da_f00dcafe);
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

/// Implement `OpaqueKeys` for a described struct.
/// Would be much nicer for this to be converted to `derive` code.
///
/// Every field type must be equivalent implement `as_ref()`, which is expected
/// to hold the standard SCALE-encoded form of that key. This is typically
/// just the bytes of the key.
///
/// ```rust
/// use sr_primitives::{impl_opaque_keys, key_types, KeyTypeId, app_crypto::{sr25519, ed25519}};
///
/// impl_opaque_keys! {
/// 	pub struct Keys {
/// 		#[id(key_types::ED25519)]
/// 		pub ed25519: ed25519::AppPublic,
/// 		#[id(key_types::SR25519)]
/// 		pub sr25519: sr25519::AppPublic,
/// 	}
/// }
/// ```
#[macro_export]
macro_rules! impl_opaque_keys {
	(
		pub struct $name:ident {
			$(
				#[id($key_id:expr)]
				pub $field:ident: $type:ty,
			)*
		}
	) => {
		#[derive(Default, Clone, PartialEq, Eq, $crate::codec::Encode, $crate::codec::Decode)]
		#[cfg_attr(feature = "std", derive(Debug, $crate::serde::Serialize, $crate::serde::Deserialize))]
		pub struct $name {
			$(
				pub $field: $type,
			)*
		}

		impl $name {
			/// Generate a set of keys with optionally using the given seed.
			///
			/// The generated key pairs are stored in the keystore.
			///
			/// Returns the concatenated SCALE encoded public keys.
			pub fn generate(seed: Option<&str>) -> $crate::rstd::vec::Vec<u8> {
				let keys = Self{
					$(
						$field: <$type as $crate::app_crypto::RuntimeAppPublic>::generate_pair(seed),
					)*
				};
				$crate::codec::Encode::encode(&keys)
			}
		}

		impl $crate::traits::OpaqueKeys for $name {
			type KeyTypeIds = $crate::rstd::iter::Cloned<
				$crate::rstd::slice::Iter<'static, $crate::KeyTypeId>
			>;

			fn key_ids() -> Self::KeyTypeIds {
				[ $($key_id),* ].iter().cloned()
			}

			fn get_raw(&self, i: $crate::KeyTypeId) -> &[u8] {
				match i {
					$( i if i == $key_id => self.$field.as_ref(), )*
					_ => &[],
				}
			}
		}
	};
}
