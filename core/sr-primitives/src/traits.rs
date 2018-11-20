// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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
use rstd::{self, result};
use runtime_io;
#[cfg(feature = "std")] use std::fmt::{Debug, Display};
#[cfg(feature = "std")] use serde::{Serialize, de::DeserializeOwned};
use substrate_primitives;
use substrate_primitives::Blake2Hasher;
use codec::{Codec, Encode, HasCompact};
pub use integer_sqrt::IntegerSquareRoot;
pub use num_traits::{Zero, One, Bounded};
pub use num_traits::ops::checked::{CheckedAdd, CheckedSub, CheckedMul, CheckedDiv};
use rstd::ops::{
	Add, Sub, Mul, Div, Rem, AddAssign, SubAssign, MulAssign, DivAssign,
	RemAssign, Shl, Shr
};

/// A lazy value.
pub trait Lazy<T: ?Sized> {
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

/// Some sort of check on the origin is performed by this object.
pub trait EnsureOrigin<OuterOrigin> {
	type Success;
	fn ensure_origin(o: OuterOrigin) -> Result<Self::Success, &'static str>;
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

/// Get the "current" block number.
pub trait CurrentHeight {
	/// The type of the block number.
	type BlockNumber;

	/// Return the current block number. Not allowed to fail.
	fn current_height(&self) -> Self::BlockNumber;
}

/// Translate a block number into a hash.
pub trait BlockNumberToHash {
	/// The type of the block number.
	type BlockNumber: Zero;

	/// The type of the hash.
	type Hash: Encode;

	/// Get the hash for a given block number, or `None` if unknown.
	fn block_number_to_hash(&self, n: Self::BlockNumber) -> Option<Self::Hash>;

	/// Get the genesis block hash; this should always be known.
	fn genesis_hash(&self) -> Self::Hash {
		self.block_number_to_hash(Zero::zero()).expect("All blockchains must know their genesis block hash; qed")
	}
}

/// Simple payment making trait, operating on a single generic `AccountId` type.
pub trait MakePayment<AccountId> {
	/// Make some sort of payment concerning `who` for an extrinsic (transaction) of encoded length
	/// `encoded_len` bytes. Return true iff the payment was successful.
	fn make_payment(who: &AccountId, encoded_len: usize) -> Result<(), &'static str>;
}

impl<T> MakePayment<T> for () {
	fn make_payment(_: &T, _: usize) -> Result<(), &'static str> { Ok(()) }
}

/// Extensible conversion trait. Generic over both source and destination types.
pub trait Convert<A, B> {
	/// Make conversion.
	fn convert(a: A) -> B;
}

/// Simple trait similar to `Into`, except that it can be used to convert numerics between each
/// other.
pub trait As<T> {
	/// Convert forward (ala `Into::into`).
	fn as_(self) -> T;
	/// Convert backward (ala `From::from`).
	fn sa(T) -> Self;
}

macro_rules! impl_numerics {
	( $( $t:ty ),* ) => {
		$(
			impl_numerics!($t: u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize,);
		)*
	};
	( $f:ty : $t:ty, $( $rest:ty, )* ) => {
		impl As<$t> for $f {
			fn as_(self) -> $t { self as $t }
			fn sa(t: $t) -> Self { t as Self }
		}
		impl_numerics!($f: $( $rest, )*);
	};
	( $f:ty : ) => {}
}

impl_numerics!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

pub struct Identity;
impl<T> Convert<T, T> for Identity {
	fn convert(a: T) -> T { a }
}
impl<T> Convert<T, ()> for () {
	fn convert(_: T) -> () { () }
}

pub trait RefInto<T> {
	fn ref_into(&self) -> &T;
}
impl<T> RefInto<T> for T {
	fn ref_into(&self) -> &T { &self }
}

pub trait SimpleArithmetic:
	Zero + One + IntegerSquareRoot + As<u64> +
	Add<Self, Output = Self> + AddAssign<Self> +
	Sub<Self, Output = Self> + SubAssign<Self> +
	Mul<Self, Output = Self> + MulAssign<Self> +
	Div<Self, Output = Self> + DivAssign<Self> +
	Rem<Self, Output = Self> + RemAssign<Self> +
	Shl<u32, Output = Self> + Shr<u32, Output = Self> +
	CheckedAdd +
	CheckedSub +
	CheckedMul +
	CheckedDiv +
	PartialOrd<Self> + Ord +
	HasCompact
{}
impl<T:
	Zero + One + IntegerSquareRoot + As<u64> +
	Add<Self, Output = Self> + AddAssign<Self> +
	Sub<Self, Output = Self> + SubAssign<Self> +
	Mul<Self, Output = Self> + MulAssign<Self> +
	Div<Self, Output = Self> + DivAssign<Self> +
	Rem<Self, Output = Self> + RemAssign<Self> +
	Shl<u32, Output = Self> + Shr<u32, Output = Self> +
	CheckedAdd +
	CheckedSub +
	CheckedMul +
	CheckedDiv +
	PartialOrd<Self> + Ord +
	HasCompact
> SimpleArithmetic for T {}

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

/// The block finalisation trait. Implementing this lets you express what should happen
/// for your module when the block is ending.
pub trait OnFinalise<BlockNumber> {
	/// The block is being finalised. Implement to have something happen.
	fn on_finalise(_n: BlockNumber) {}
}

impl<N> OnFinalise<N> for () {}

macro_rules! tuple_impl {
	($one:ident,) => {
		impl<Number: Copy, $one: OnFinalise<Number>> OnFinalise<Number> for ($one,) {
			fn on_finalise(n: Number) {
				$one::on_finalise(n);
			}
		}
	};
	($first:ident, $($rest:ident,)+) => {
		impl<
			Number: Copy,
			$first: OnFinalise<Number>,
			$($rest: OnFinalise<Number>),+
		> OnFinalise<Number> for ($first, $($rest),+) {
			fn on_finalise(n: Number) {
				$first::on_finalise(n);
				$($rest::on_finalise(n);)+
			}
		}
		tuple_impl!($($rest,)+);
	}
}

#[allow(non_snake_case)]
tuple_impl!(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z,);

/// Abstraction around hashing
pub trait Hash: 'static + MaybeSerializeDebug + Clone + Eq + PartialEq {	// Stupid bug in the Rust compiler believes derived
																	// traits must be fulfilled by all type parameters.
	/// The hash type produced.
	type Output: Member + MaybeSerializeDebug + AsRef<[u8]> + AsMut<[u8]>;

	/// Produce the hash of some byte-slice.
	fn hash(s: &[u8]) -> Self::Output;

	/// Produce the hash of some codec-encodable value.
	fn hash_of<S: Codec>(s: &S) -> Self::Output {
		Encode::using_encoded(s, Self::hash)
	}

	/// Produce the trie-db root of a mapping from indices to byte slices.
	fn enumerated_trie_root(items: &[&[u8]]) -> Self::Output;

	/// Iterator-based version of `enumerated_trie_root`.
	fn ordered_trie_root<
		I: IntoIterator<Item = A> + Iterator<Item = A>,
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
	fn storage_changes_root(parent_hash: Self::Output, parent_number: u64) -> Option<Self::Output>;
}

/// Blake2-256 Hash implementation.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct BlakeTwo256;

impl Hash for BlakeTwo256 {
	type Output = substrate_primitives::H256;
	fn hash(s: &[u8]) -> Self::Output {
		runtime_io::blake2_256(s).into()
	}
	fn enumerated_trie_root(items: &[&[u8]]) -> Self::Output {
		runtime_io::enumerated_trie_root::<Blake2Hasher>(items).into()
	}
	fn trie_root<
		I: IntoIterator<Item = (A, B)>,
		A: AsRef<[u8]> + Ord,
		B: AsRef<[u8]>
	>(input: I) -> Self::Output {
		runtime_io::trie_root::<Blake2Hasher, _, _, _>(input).into()
	}
	fn ordered_trie_root<
		I: IntoIterator<Item = A> + Iterator<Item = A>,
		A: AsRef<[u8]>
	>(input: I) -> Self::Output {
		runtime_io::ordered_trie_root::<Blake2Hasher, _, _>(input).into()
	}
	fn storage_root() -> Self::Output {
		runtime_io::storage_root().into()
	}
	fn storage_changes_root(parent_hash: Self::Output, parent_number: u64) -> Option<Self::Output> {
		runtime_io::storage_changes_root(parent_hash.into(), parent_number).map(Into::into)
	}
}

/// Something that can be checked for equality and printed out to a debug channel if bad.
pub trait CheckEqual {
	fn check_equal(&self, other: &Self);
}

impl CheckEqual for substrate_primitives::H256 {
	#[cfg(feature = "std")]
	fn check_equal(&self, other: &Self) {
		use substrate_primitives::hexdisplay::HexDisplay;
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

impl<I> CheckEqual for I where I: DigestItem {
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

#[cfg(feature = "std")]
pub trait MaybeSerializeDebugButNotDeserialize: Serialize + Debug {}
#[cfg(feature = "std")]
impl<T: Serialize + Debug> MaybeSerializeDebugButNotDeserialize for T {}

#[cfg(not(feature = "std"))]
pub trait MaybeSerializeDebugButNotDeserialize {}
#[cfg(not(feature = "std"))]
impl<T> MaybeSerializeDebugButNotDeserialize for T {}

#[cfg(feature = "std")]
pub trait MaybeSerialize: Serialize {}
#[cfg(feature = "std")]
impl<T: Serialize> MaybeSerialize for T {}

#[cfg(not(feature = "std"))]
pub trait MaybeSerialize {}
#[cfg(not(feature = "std"))]
impl<T> MaybeSerialize for T {}

#[cfg(feature = "std")]
pub trait MaybeSerializeDebug: Serialize + DeserializeOwned + Debug {}
#[cfg(feature = "std")]
impl<T: Serialize + DeserializeOwned + Debug> MaybeSerializeDebug for T {}

#[cfg(not(feature = "std"))]
pub trait MaybeSerializeDebug {}
#[cfg(not(feature = "std"))]
impl<T> MaybeSerializeDebug for T {}

#[cfg(feature = "std")]
pub trait MaybeDebug: Debug {}
#[cfg(feature = "std")]
impl<T: Debug> MaybeDebug for T {}

#[cfg(not(feature = "std"))]
pub trait MaybeDebug {}
#[cfg(not(feature = "std"))]
impl<T> MaybeDebug for T {}

#[cfg(feature = "std")]
pub trait MaybeDisplay: Display {}
#[cfg(feature = "std")]
impl<T: Display> MaybeDisplay for T {}

#[cfg(not(feature = "std"))]
pub trait MaybeDisplay {}
#[cfg(not(feature = "std"))]
impl<T> MaybeDisplay for T {}

#[cfg(feature = "std")]
pub trait MaybeDecode: ::codec::Decode {}
#[cfg(feature = "std")]
impl<T: ::codec::Decode> MaybeDecode for T {}

#[cfg(not(feature = "std"))]
pub trait MaybeDecode {}
#[cfg(not(feature = "std"))]
impl<T> MaybeDecode for T {}

pub trait Member: Send + Sync + Sized + MaybeDebug + Eq + PartialEq + Clone + 'static {}
impl<T: Send + Sync + Sized + MaybeDebug + Eq + PartialEq + Clone + 'static> Member for T {}

/// Something which fulfills the abstract idea of a Substrate header. It has types for a `Number`,
/// a `Hash` and a `Digest`. It provides access to an `extrinsics_root`, `state_root` and
/// `parent_hash`, as well as a `digest` and a block `number`.
///
/// You can also create a `new` one from those fields.
pub trait Header: Clone + Send + Sync + Codec + Eq + MaybeSerializeDebug + 'static {
	type Number: Member + MaybeSerializeDebug + ::rstd::hash::Hash + Copy + MaybeDisplay + SimpleArithmetic + Codec;
	type Hash: Member + MaybeSerializeDebug + ::rstd::hash::Hash + Copy + MaybeDisplay + Default + SimpleBitOps + Codec + AsRef<[u8]> + AsMut<[u8]>;
	type Hashing: Hash<Output = Self::Hash>;
	type Digest: Digest<Hash = Self::Hash>;

	fn new(
		number: Self::Number,
		extrinsics_root: Self::Hash,
		state_root: Self::Hash,
		parent_hash: Self::Hash,
		digest: Self::Digest
	) -> Self;

	fn number(&self) -> &Self::Number;
	fn set_number(&mut self, Self::Number);

	fn extrinsics_root(&self) -> &Self::Hash;
	fn set_extrinsics_root(&mut self, Self::Hash);

	fn state_root(&self) -> &Self::Hash;
	fn set_state_root(&mut self, Self::Hash);

	fn parent_hash(&self) -> &Self::Hash;
	fn set_parent_hash(&mut self, Self::Hash);

	fn digest(&self) -> &Self::Digest;
	/// Get a mutable reference to the digest.
	fn digest_mut(&mut self) -> &mut Self::Digest;
	fn set_digest(&mut self, Self::Digest);

	fn hash(&self) -> Self::Hash {
		<Self::Hashing as Hash>::hash_of(self)
	}
}

/// Something which fulfills the abstract idea of a Substrate block. It has types for an
/// `Extrinsic` piece of information as well as a `Header`.
///
/// You can get an iterator over each of the `extrinsics` and retrieve the `header`.
pub trait Block: Clone + Send + Sync + Codec + Eq + MaybeSerializeDebug + 'static {
	type Extrinsic: Member + Codec + Extrinsic + MaybeSerialize;
	type Header: Header<Hash=Self::Hash>;
	type Hash: Member + MaybeSerializeDebug + ::rstd::hash::Hash + Copy + MaybeDisplay + Default + SimpleBitOps + Codec + AsRef<[u8]> + AsMut<[u8]>;

	fn header(&self) -> &Self::Header;
	fn extrinsics(&self) -> &[Self::Extrinsic];
	fn deconstruct(self) -> (Self::Header, Vec<Self::Extrinsic>);
	fn new(header: Self::Header, extrinsics: Vec<Self::Extrinsic>) -> Self;
	fn hash(&self) -> Self::Hash {
		<<Self::Header as Header>::Hashing as Hash>::hash_of(self.header())
	}
}

/// Something that acts like an `Extrinsic`.
pub trait Extrinsic {
	/// Is this `Extrinsic` signed?
	/// If no information are available about signed/unsigned, `None` should be returned.
	fn is_signed(&self) -> Option<bool> { None }
}

/// Extract the hashing type for a block.
pub type HashFor<B> = <<B as Block>::Header as Header>::Hashing;
/// Extract the number type for a block.
pub type NumberFor<B> = <<B as Block>::Header as Header>::Number;
/// Extract the digest type for a block.
pub type DigestFor<B> = <<B as Block>::Header as Header>::Digest;
/// Extract the digest item type for a block.
pub type DigestItemFor<B> = <DigestFor<B> as Digest>::Item;

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

/// An "executable" piece of information, used by the standard Substrate Executive in order to
/// enact a piece of extrinsic information by marshalling and dispatching to a named functioon
/// call.
///
/// Also provides information on to whom this information is attributable and an index that allows
/// each piece of attributable information to be disambiguated.
pub trait Applyable: Sized + Send + Sync {
	type AccountId: Member + MaybeDisplay;
	type Index: Member + MaybeDisplay + SimpleArithmetic;
	type Call: Member;
	fn index(&self) -> Option<&Self::Index>;
	fn sender(&self) -> Option<&Self::AccountId>;
	fn deconstruct(self) -> (Self::Call, Option<Self::AccountId>);
}

/// Something that acts like a `Digest` - it can have `Log`s `push`ed onto it and these `Log`s are
/// each `Codec`.
pub trait Digest: Member + MaybeSerializeDebugButNotDeserialize + Default {
	type Hash: Member + MaybeSerializeDebugButNotDeserialize;
	type Item: DigestItem<Hash = Self::Hash>;

	/// Get reference to all digest items.
	fn logs(&self) -> &[Self::Item];
	/// Push new digest item.
	fn push(&mut self, item: Self::Item);
	/// Pop a digest item.
	fn pop(&mut self) -> Option<Self::Item>;

	/// Get reference to the first digest item that matches the passed predicate.
	fn log<T, F: Fn(&Self::Item) -> Option<&T>>(&self, predicate: F) -> Option<&T> {
		self.logs().iter()
			.filter_map(predicate)
			.next()
	}
}

/// Single digest item. Could be any type that implements `Member` and provides methods
/// for casting member to 'system' log items, known to substrate.
///
/// If the runtime does not supports some 'system' items, use `()` as a stub.
pub trait DigestItem: Codec + Member + MaybeSerializeDebugButNotDeserialize {
	type Hash: Member + MaybeSerializeDebugButNotDeserialize;
	type AuthorityId: Member + MaybeSerializeDebugButNotDeserialize;

	/// Returns Some if the entry is the `AuthoritiesChange` entry.
	fn as_authorities_change(&self) -> Option<&[Self::AuthorityId]>;

	/// Returns Some if the entry is the `ChangesTrieRoot` entry.
	fn as_changes_trie_root(&self) -> Option<&Self::Hash>;
}

/// Something that provides an inherent for a runtime.
pub trait ProvideInherent {
	/// The inherent that is provided.
	type Inherent: Encode + MaybeDecode;
	/// The error used by this trait.
	type Error: Encode + MaybeDecode;
	/// The call for setting the inherent.
	type Call: Encode + MaybeDecode;

	/// Create the inherent extrinsics.
	///
	/// # Return
	///
	/// Returns a vector with tuples containing the index for the extrinsic and the extrinsic itself.
	fn create_inherent_extrinsics(data: Self::Inherent) -> Vec<(u32, Self::Call)>;

	/// Check that the given inherent is valid.
	fn check_inherent<Block: self::Block, F: Fn(&Block::Extrinsic) -> Option<&Self::Call>>(
		block: &Block, data: Self::Inherent, extract_function: &F
	) -> Result<(), Self::Error>;
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

/// A marker trait for something that knows the type of the node block.
pub trait GetNodeBlockType {
	/// The `NodeBlock` type.
	type NodeBlock: self::Block;
}
