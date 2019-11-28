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
use rstd::{self, result, marker::PhantomData, convert::{TryFrom, TryInto}, fmt::Debug};
use runtime_io;
#[cfg(feature = "std")]
use std::fmt::Display;
#[cfg(feature = "std")]
use serde::{Serialize, Deserialize, de::DeserializeOwned};
use primitives::{self, Hasher, Blake2Hasher, TypeId};
use crate::codec::{Codec, Encode, Decode};
use crate::transaction_validity::{
	ValidTransaction, TransactionValidity, TransactionValidityError, UnknownTransaction,
};
use crate::generic::{Digest, DigestItem};
pub use arithmetic::traits::{
	SimpleArithmetic, UniqueSaturatedInto, UniqueSaturatedFrom, Saturating, SaturatedConversion,
	Zero, One, Bounded, CheckedAdd, CheckedSub, CheckedMul, CheckedDiv,
	CheckedShl, CheckedShr, IntegerSquareRoot
};
use app_crypto::AppKey;
use impl_trait_for_tuples::impl_for_tuples;

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

/// Some type that is able to be collapsed into an account ID. It is not possible to recreate the original value from
/// the account ID.
pub trait IdentifyAccount {
	/// The account ID that this can be transformed into.
	type AccountId;
	/// Transform into an account.
	fn into_account(self) -> Self::AccountId;
}

impl IdentifyAccount for primitives::ed25519::Public {
	type AccountId = Self;
	fn into_account(self) -> Self { self }
}

impl IdentifyAccount for primitives::sr25519::Public {
	type AccountId = Self;
	fn into_account(self) -> Self { self }
}

impl IdentifyAccount for primitives::ecdsa::Public {
	type AccountId = Self;
	fn into_account(self) -> Self { self }
}

/// Means of signature verification.
pub trait Verify {
	/// Type of the signer.
	type Signer: IdentifyAccount;
	/// Verify a signature. Return `true` if signature is valid for the value.
	fn verify<L: Lazy<[u8]>>(&self, msg: L, signer: &<Self::Signer as IdentifyAccount>::AccountId) -> bool;
}

impl Verify for primitives::ed25519::Signature {
	type Signer = primitives::ed25519::Public;
	fn verify<L: Lazy<[u8]>>(&self, mut msg: L, signer: &primitives::ed25519::Public) -> bool {
		runtime_io::crypto::ed25519_verify(self, msg.get(), signer)
	}
}

impl Verify for primitives::sr25519::Signature {
	type Signer = primitives::sr25519::Public;
	fn verify<L: Lazy<[u8]>>(&self, mut msg: L, signer: &primitives::sr25519::Public) -> bool {
		runtime_io::crypto::sr25519_verify(self, msg.get(), signer)
	}
}

impl Verify for primitives::ecdsa::Signature {
	type Signer = primitives::ecdsa::Public;
	fn verify<L: Lazy<[u8]>>(&self, mut msg: L, signer: &primitives::ecdsa::Public) -> bool {
		match runtime_io::crypto::secp256k1_ecdsa_recover_compressed(
			self.as_ref(),
			&runtime_io::hashing::blake2_256(msg.get()),
		) {
			Ok(pubkey) => <dyn AsRef<[u8]>>::as_ref(signer) == &pubkey[..],
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
	S: Verify<Signer=<<T as AppKey>::Public as app_crypto::AppPublic>::Generic> + From<T>,
	T: app_crypto::Wraps<Inner=S> + app_crypto::AppKey + app_crypto::AppSignature +
		AsRef<S> + AsMut<S> + From<S>,
> AppVerify for T where
	<S as Verify>::Signer: IdentifyAccount<AccountId = <S as Verify>::Signer>,
	<<T as AppKey>::Public as app_crypto::AppPublic>::Generic:
		IdentifyAccount<AccountId = <<T as AppKey>::Public as app_crypto::AppPublic>::Generic>,
{
	type AccountId = <T as AppKey>::Public;
	fn verify<L: Lazy<[u8]>>(&self, msg: L, signer: &<T as AppKey>::Public) -> bool {
		use app_crypto::IsWrappedBy;
		let inner: &S = self.as_ref();
		let inner_pubkey = <<T as AppKey>::Public as app_crypto::AppPublic>::Generic::from_ref(&signer);
		Verify::verify(inner, msg, inner_pubkey)
	}
}

/// An error type that indicates that the origin is invalid.
#[derive(Encode, Decode)]
pub struct InvalidOrigin;

impl From<InvalidOrigin> for &'static str {
	fn from(_: InvalidOrigin) -> &'static str {
		"Invalid origin"
	}
}

/// Some sort of check on the origin is performed by this object.
pub trait EnsureOrigin<OuterOrigin> {
	/// A return type.
	type Success;
	/// Perform the origin check.
	fn ensure_origin(o: OuterOrigin) -> result::Result<Self::Success, InvalidOrigin> {
		Self::try_origin(o).map_err(|_| InvalidOrigin)
	}
	/// Perform the origin check.
	fn try_origin(o: OuterOrigin) -> result::Result<Self::Success, OuterOrigin>;
}

/// An error that indicates that a lookup failed.
#[derive(Encode, Decode)]
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
	type Source: Codec + Clone + PartialEq + Debug;
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
impl<T: Codec + Clone + PartialEq + Debug> StaticLookup for IdentityLookup<T> {
	type Source = T;
	type Target = T;
	fn lookup(x: T) -> Result<T, LookupError> { Ok(x) }
	fn unlookup(x: T) -> T { x }
}

impl<T> Lookup for IdentityLookup<T> {
	type Source = T;
	type Target = T;
	fn lookup(&self, x: T) -> Result<T, LookupError> { Ok(x) }
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
#[impl_for_tuples(30)]
pub trait OnFinalize<BlockNumber> {
	/// The block is being finalized. Implement to have something happen.
	fn on_finalize(_n: BlockNumber) {}
}

/// The block initialization trait. Implementing this lets you express what should happen
/// for your module when the block is beginning (right before the first extrinsic is executed).
#[impl_for_tuples(30)]
pub trait OnInitialize<BlockNumber> {
	/// The block is being initialized. Implement to have something happen.
	fn on_initialize(_n: BlockNumber) {}
}

/// Off-chain computation trait.
///
/// Implementing this trait on a module allows you to perform long-running tasks
/// that make validators generate extrinsics (either transactions or inherents)
/// with the results of those long-running computations.
///
/// NOTE: This function runs off-chain, so it can access the block state,
/// but cannot preform any alterations.
#[impl_for_tuples(30)]
pub trait OffchainWorker<BlockNumber> {
	/// This function is being called on every block.
	///
	/// Implement this and use special `extern`s to generate transactions or inherents.
	/// Any state alterations are lost and are not persisted.
	fn generate_extrinsics(_n: BlockNumber) {}
}

/// Abstraction around hashing
// Stupid bug in the Rust compiler believes derived
// traits must be fulfilled by all type parameters.
pub trait Hash: 'static + MaybeSerializeDeserialize + Debug + Clone + Eq + PartialEq {
	/// The hash type produced.
	type Output: Member + MaybeSerializeDeserialize + Debug + rstd::hash::Hash
		+ AsRef<[u8]> + AsMut<[u8]> + Copy + Default + Encode + Decode;

	/// The associated hash_db Hasher type.
	type Hasher: Hasher<Out=Self::Output>;

	/// Produce the hash of some byte-slice.
	fn hash(s: &[u8]) -> Self::Output;

	/// Produce the hash of some codec-encodable value.
	fn hash_of<S: Encode>(s: &S) -> Self::Output {
		Encode::using_encoded(s, Self::hash)
	}

	/// The ordered Patricia tree root of the given `input`.
	fn ordered_trie_root(input: Vec<Vec<u8>>) -> Self::Output;

	/// The Patricia tree root of the given mapping.
	fn trie_root(input: Vec<(Vec<u8>, Vec<u8>)>) -> Self::Output;
}

/// Blake2-256 Hash implementation.
#[derive(PartialEq, Eq, Clone, primitives::RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct BlakeTwo256;

impl Hash for BlakeTwo256 {
	type Output = primitives::H256;
	type Hasher = Blake2Hasher;
	fn hash(s: &[u8]) -> Self::Output {
		runtime_io::hashing::blake2_256(s).into()
	}

	fn trie_root(input: Vec<(Vec<u8>, Vec<u8>)>) -> Self::Output {
		runtime_io::trie::blake2_256_root(input)
	}

	fn ordered_trie_root(input: Vec<Vec<u8>>) -> Self::Output {
		runtime_io::trie::blake2_256_ordered_root(input)
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

impl<H: PartialEq + Eq + Debug> CheckEqual for super::generic::DigestItem<H> where H: Encode {
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

macro_rules! impl_maybe_marker {
	( $( $(#[$doc:meta])+ $trait_name:ident: $($trait_bound:path),+ );+ ) => {
		$(
			$(#[$doc])+
			#[cfg(feature = "std")]
			pub trait $trait_name: $($trait_bound +)+ {}
			#[cfg(feature = "std")]
			impl<T: $($trait_bound +)+> $trait_name for T {}

			$(#[$doc])+
			#[cfg(not(feature = "std"))]
			pub trait $trait_name {}
			#[cfg(not(feature = "std"))]
			impl<T> $trait_name for T {}
		)+
	}
}

impl_maybe_marker!(
	/// A type that implements Display when in std environment.
	MaybeDisplay: Display;

	/// A type that implements Hash when in std environment.
	MaybeHash: rstd::hash::Hash;

	/// A type that implements Serialize when in std environment.
	MaybeSerialize: Serialize;

	/// A type that implements Serialize, DeserializeOwned and Debug when in std environment.
	MaybeSerializeDeserialize: DeserializeOwned, Serialize
);

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
	type Number: Member + MaybeSerializeDeserialize + Debug + rstd::hash::Hash
		+ Copy + MaybeDisplay + SimpleArithmetic + Codec;
	/// Header hash type
	type Hash: Member + MaybeSerializeDeserialize + Debug + rstd::hash::Hash
		+ Copy + MaybeDisplay + Default + SimpleBitOps + Codec + AsRef<[u8]> + AsMut<[u8]>;
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
pub trait Block: Clone + Send + Sync + Codec + Eq + MaybeSerialize + Debug + 'static {
	/// Type of extrinsics.
	type Extrinsic: Member + Codec + Extrinsic + MaybeSerialize;
	/// Header type.
	type Header: Header<Hash=Self::Hash>;
	/// Block hash type.
	type Hash: Member + MaybeSerializeDeserialize + Debug + rstd::hash::Hash
		+ Copy + MaybeDisplay + Default + SimpleBitOps + Codec + AsRef<[u8]> + AsMut<[u8]>;

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
	/// Create an encoded block from the given `header` and `extrinsics` without requiring to create an instance.
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
	fn is_signed(&self) -> Option<bool> { None }

	/// Create new instance of the extrinsic.
	///
	/// Extrinsics can be split into:
	/// 1. Inherents (no signature; created by validators during block production)
	/// 2. Unsigned Transactions (no signature; represent "system calls" or other special kinds of calls)
	/// 3. Signed Transactions (with signature; a regular transactions with known origin)
	fn new(_call: Self::Call, _signed_data: Option<Self::SignaturePayload>) -> Option<Self> { None }
}

/// Extract the hashing type for a block.
pub type HashFor<B> = <<B as Block>::Header as Header>::Hashing;
/// Extract the number type for a block.
pub type NumberFor<B> = <<B as Block>::Header as Header>::Number;
/// Extract the digest type for a block.
pub type DigestFor<B> = Digest<<<B as Block>::Header as Header>::Hash>;
/// Extract the digest item type for a block.
pub type DigestItemFor<B> = DigestItem<<<B as Block>::Header as Header>::Hash>;

/// A "checkable" piece of information, used by the standard Substrate Executive in order to
/// check the validity of a piece of extrinsic information, usually by verifying the signature.
/// Implement for pieces of information that require some additional context `Context` in order to be
/// checked.
pub trait Checkable<Context>: Sized {
	/// Returned if `check` succeeds.
	type Checked;

	/// Check self, given an instance of Context.
	fn check(self, c: &Context) -> Result<Self::Checked, TransactionValidityError>;
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
}

/// Result of a module function call; either nothing (functions are only called for "side effects")
/// or an error message.
pub type DispatchResult<Error> = result::Result<(), Error>;

/// A lazy call (module function and argument values) that can be executed via its `dispatch`
/// method.
pub trait Dispatchable {
	/// Every function call from your runtime has an origin, which specifies where the extrinsic was
	/// generated from. In the case of a signed extrinsic (transaction), the origin contains an
	/// identifier for the caller. The origin can be empty in the case of an inherent extrinsic.
	type Origin;
	/// ...
	type Trait;
	/// The error type returned by this dispatchable.
	type Error: Into<crate::DispatchError>;
	/// Actually dispatch this call and result the result of it.
	fn dispatch(self, origin: Self::Origin) -> DispatchResult<Self::Error>;
}

/// Means by which a transaction may be extended. This type embodies both the data and the logic
/// that should be additionally associated with the transaction. It should be plain old data.
pub trait SignedExtension: Codec + Debug + Sync + Send + Clone + Eq + PartialEq {
	/// The type which encodes the sender identity.
	type AccountId;

	/// The type which encodes the call to be dispatched.
	type Call;

	/// Any additional data that will go into the signed payload. This may be created dynamically
	/// from the transaction using the `additional_signed` function.
	type AdditionalSigned: Encode;

	/// The type that encodes information that can be passed from pre_dispatch to post-dispatch.
	type Pre: Default;

	/// An opaque set of information attached to the transaction. This could be constructed anywhere
	/// down the line in a runtime. The current substrate runtime uses a struct with the same name
	/// to represent the dispatch class and weight.
	type DispatchInfo: Clone;

	/// Construct any additional data that should be in the signed payload of the transaction. Can
	/// also perform any pre-signature-verification checks and return an error if needed.
	fn additional_signed(&self) -> Result<Self::AdditionalSigned, TransactionValidityError>;

	/// Validate a signed transaction for the transaction queue.
	///
	/// This function can be called frequently by the transaction queue,
	/// to obtain transaction validity against current state.
	/// It should perform all checks that determine a valid transaction,
	/// that can pay for it's execution and quickly eliminate ones
	/// that are stale or incorrect.
	///
	/// Make sure to perform the same checks in `pre_dispatch` function.
	fn validate(
		&self,
		_who: &Self::AccountId,
		_call: &Self::Call,
		_info: Self::DispatchInfo,
		_len: usize,
	) -> TransactionValidity {
		Ok(ValidTransaction::default())
	}

	/// Do any pre-flight stuff for a signed transaction.
	///
	/// Note this function by default delegates to `validate`, so that
	/// all checks performed for the transaction queue are also performed during
	/// the dispatch phase (applying the extrinsic).
	///
	/// If you ever override this function, you need to make sure to always
	/// perform the same validation as in `validate`.
	fn pre_dispatch(
		self,
		who: &Self::AccountId,
		call: &Self::Call,
		info: Self::DispatchInfo,
		len: usize,
	) -> Result<Self::Pre, TransactionValidityError> {
		self.validate(who, call, info.clone(), len)
			.map(|_| Self::Pre::default())
			.map_err(Into::into)
	}

	/// Validate an unsigned transaction for the transaction queue.
	///
	/// This function can be called frequently by the transaction queue,
	/// to obtain transaction validity against current state.
	/// It should perform all checks that determine a valid unsigned transaction,
	/// and quickly eliminate ones that are stale or incorrect.
	///
	/// Make sure to perform the same checks in `pre_dispatch_unsigned` function.
	fn validate_unsigned(
		_call: &Self::Call,
		_info: Self::DispatchInfo,
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
		info: Self::DispatchInfo,
		len: usize,
	) -> Result<Self::Pre, TransactionValidityError> {
		Self::validate_unsigned(call, info.clone(), len)
			.map(|_| Self::Pre::default())
			.map_err(Into::into)
	}

	/// Do any post-flight stuff for a transaction.
	fn post_dispatch(_pre: Self::Pre, _info: Self::DispatchInfo, _len: usize) { }
}

/// An error that is returned by a dispatchable function of a module.
pub trait ModuleDispatchError {
	/// Convert this error to an `u8`.
	///
	/// The `u8` corresponds to the index of the variant in the error enum.
	fn as_u8(&self) -> u8;

	/// Convert the error to a `&'static str`.
	fn as_str(&self) -> &'static str;
}

#[impl_for_tuples(1, 12)]
impl<AccountId, Call, Info: Clone> SignedExtension for Tuple {
	for_tuples!( where #( Tuple: SignedExtension<AccountId=AccountId, Call=Call, DispatchInfo=Info> )* );
	type AccountId = AccountId;
	type Call = Call;
	type DispatchInfo = Info;
	for_tuples!( type AdditionalSigned = ( #( Tuple::AdditionalSigned ),* ); );
	for_tuples!( type Pre = ( #( Tuple::Pre ),* ); );

	fn additional_signed(&self) -> Result<Self::AdditionalSigned, TransactionValidityError> {
		Ok(for_tuples!( ( #( Tuple.additional_signed()? ),* ) ))
	}

	fn validate(
		&self,
		who: &Self::AccountId,
		call: &Self::Call,
		info: Self::DispatchInfo,
		len: usize,
	) -> TransactionValidity {
		let valid = ValidTransaction::default();
		for_tuples!( #( let valid = valid.combine_with(Tuple.validate(who, call, info.clone(), len)?); )* );
		Ok(valid)
	}

	fn pre_dispatch(self, who: &Self::AccountId, call: &Self::Call, info: Self::DispatchInfo, len: usize)
		-> Result<Self::Pre, TransactionValidityError>
	{
		Ok(for_tuples!( ( #( Tuple.pre_dispatch(who, call, info.clone(), len)? ),* ) ))
	}

	fn validate_unsigned(
		call: &Self::Call,
		info: Self::DispatchInfo,
		len: usize,
	) -> TransactionValidity {
		let valid = ValidTransaction::default();
		for_tuples!( #( let valid = valid.combine_with(Tuple::validate_unsigned(call, info.clone(), len)?); )* );
		Ok(valid)
	}

	fn pre_dispatch_unsigned(
		call: &Self::Call,
		info: Self::DispatchInfo,
		len: usize,
	) -> Result<Self::Pre, TransactionValidityError> {
		Ok(for_tuples!( ( #( Tuple::pre_dispatch_unsigned(call, info.clone(), len)? ),* ) ))
	}

	fn post_dispatch(
		pre: Self::Pre,
		info: Self::DispatchInfo,
		len: usize,
	) {
		for_tuples!( #( Tuple::post_dispatch(pre.Tuple, info.clone(), len); )* )
	}
}

/// Only for bare bone testing when you don't care about signed extensions at all.
#[cfg(feature = "std")]
impl SignedExtension for () {
	type AccountId = u64;
	type AdditionalSigned = ();
	type Call = ();
	type Pre = ();
	type DispatchInfo = ();
	fn additional_signed(&self) -> rstd::result::Result<(), TransactionValidityError> { Ok(()) }
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

	/// An opaque set of information attached to the transaction.
	type DispatchInfo: Clone;

	/// Returns a reference to the sender if any.
	fn sender(&self) -> Option<&Self::AccountId>;

	/// Checks to see if this is a valid *transaction*. It returns information on it if so.
	#[allow(deprecated)] // Allow ValidateUnsigned
	fn validate<V: ValidateUnsigned<Call=Self::Call>>(
		&self,
		info: Self::DispatchInfo,
		len: usize,
	) -> TransactionValidity;

	/// Executes all necessary logic needed prior to dispatch and deconstructs into function call,
	/// index and sender.
	#[allow(deprecated)] // Allow ValidateUnsigned
	fn apply<V: ValidateUnsigned<Call=Self::Call>>(
		self,
		info: Self::DispatchInfo,
		len: usize,
	) -> crate::ApplyExtrinsicResult;
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

/// Something that can validate unsigned extrinsics for the transaction pool.
///
/// Note that any checks done here are only used for determining the validity of
/// the transaction for the transaction pool.
/// During block execution phase one need to perform the same checks anyway,
/// since this function is not being called.
#[deprecated(note = "Use SignedExtensions instead.")]
pub trait ValidateUnsigned {
	/// The call to validate
	type Call;

	/// Validate the call right before dispatch.
	///
	/// This method should be used to prevent transactions already in the pool
	/// (i.e. passing `validate_unsigned`) from being included in blocks
	/// in case we know they now became invalid.
	///
	/// By default it's a good idea to call `validate_unsigned` from within
	/// this function again to make sure we never include an invalid transaction.
	///
	/// Changes made to storage WILL be persisted if the call returns `Ok`.
	fn pre_dispatch(call: &Self::Call) -> Result<(), TransactionValidityError> {
		Self::validate_unsigned(call)
			.map(|_| ())
			.map_err(Into::into)
	}

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
	/// Types bound to this opaque keys that provide the key type ids returned.
	type KeyTypeIdProviders;

	/// Return the key-type IDs supported by this set.
	fn key_ids() -> &'static [crate::KeyTypeId];
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
pub struct TrailingZeroInput<'a>(&'a [u8]);

impl<'a> TrailingZeroInput<'a> {
	/// Create a new instance from the given byte array.
	pub fn new(data: &'a [u8]) -> Self {
		Self(data)
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
///
/// Every field type must implement [`BoundToRuntimeAppPublic`](crate::BoundToRuntimeAppPublic).
/// `KeyTypeIdProviders` is set to the types given as fields.
///
/// ```rust
/// use sr_primitives::{
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
macro_rules! impl_opaque_keys {
	(
		pub struct $name:ident {
			$(
				pub $field:ident: $type:ty,
			)*
		}
	) => {
		#[derive(
			Default, Clone, PartialEq, Eq,
			$crate::codec::Encode,
			$crate::codec::Decode,
			$crate::RuntimeDebug,
		)]
		#[cfg_attr(feature = "std", derive($crate::serde::Serialize, $crate::serde::Deserialize))]
		pub struct $name {
			$(
				pub $field: <$type as $crate::BoundToRuntimeAppPublic>::Public,
			)*
		}

		impl $name {
			/// Generate a set of keys with optionally using the given seed.
			///
			/// The generated key pairs are stored in the keystore.
			///
			/// Returns the concatenated SCALE encoded public keys.
			pub fn generate(seed: Option<$crate::rstd::vec::Vec<u8>>) -> $crate::rstd::vec::Vec<u8> {
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

/// Trait for things which can be printed from the runtime.
pub trait Printable {
	/// Print the object.
	fn print(&self);
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
		runtime_io::misc::print_num(*self);
	}
}

impl Printable for &[u8] {
	fn print(&self) {
		runtime_io::misc::print_hex(self);
	}
}

impl Printable for &str {
	fn print(&self) {
		runtime_io::misc::print_utf8(self.as_bytes());
	}
}

#[impl_for_tuples(1, 12)]
impl Printable for Tuple {
	fn print(&self) {
		for_tuples!( #( Tuple.print(); )* )
	}
}

/// Something that can convert a [`BlockId`] to a number or a hash.
#[cfg(feature = "std")]
pub trait BlockIdTo<Block: self::Block> {
	/// The error type that will be returned by the functions.
	type Error: std::fmt::Debug;

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

#[cfg(test)]
mod tests {
	use super::AccountIdConversion;
	use crate::codec::{Encode, Decode, Input};

	mod t {
		use primitives::crypto::KeyTypeId;
		use app_crypto::{app_crypto, sr25519};
		app_crypto!(sr25519, KeyTypeId(*b"test"));
	}

	#[test]
	fn app_verify_works() {
		use t::*;
		use super::AppVerify;

		let s = Signature::default();
		let _ = s.verify(&[0u8; 100][..], &Public::default());
	}

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
