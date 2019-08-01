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

//! Runtime Modules shared primitive types.

#![warn(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

#[doc(hidden)]
pub use codec;
#[cfg(feature = "std")]
#[doc(hidden)]
pub use serde;
#[doc(hidden)]
pub use rstd;

#[doc(hidden)]
pub use paste;

#[cfg(feature = "std")]
pub use runtime_io::{StorageOverlay, ChildrenStorageOverlay};

use rstd::{prelude::*, ops, convert::TryInto};
use primitives::{crypto, ed25519, sr25519, hash::{H256, H512}};
use codec::{Encode, Decode};

#[cfg(feature = "std")]
pub mod testing;

pub mod weights;
pub mod traits;
pub mod generic;
pub mod transaction_validity;
pub mod sr_arithmetic;

use traits::{SaturatedConversion, UniqueSaturatedInto, Saturating, Bounded, CheckedSub, CheckedAdd};

/// Re-export these since they're only "kind of" generic.
pub use generic::{DigestItem, Digest};

/// Re-export this since it's part of the API of this crate.
pub use primitives::crypto::{key_types, KeyTypeId};

/// Export arithmetic stuff.
pub use sr_arithmetic::{Perbill, Permill};

/// A message indicating an invalid signature in extrinsic.
pub const BAD_SIGNATURE: &str = "bad signature in extrinsic";

/// Full block error message.
///
/// This allows modules to indicate that given transaction is potentially valid
/// in the future, but can't be executed in the current state.
/// Note this error should be returned early in the execution to prevent DoS,
/// cause the fees are not being paid if this error is returned.
///
/// Example: block gas limit is reached (the transaction can be retried in the next block though).
pub const BLOCK_FULL: &str = "block size limit is reached";

/// Justification type.
pub type Justification = Vec<u8>;

use traits::{Verify, Lazy};

/// A module identifier. These are per module and should be stored in a registry somewhere.
#[derive(Clone, Copy, Eq, PartialEq, Encode, Decode)]
pub struct ModuleId(pub [u8; 8]);

impl traits::TypeId for ModuleId {
	const TYPE_ID: [u8; 4] = *b"modl";
}

/// A String that is a `&'static str` on `no_std` and a `Cow<'static, str>` on `std`.
#[cfg(feature = "std")]
pub type RuntimeString = ::std::borrow::Cow<'static, str>;
/// A String that is a `&'static str` on `no_std` and a `Cow<'static, str>` on `std`.
#[cfg(not(feature = "std"))]
pub type RuntimeString = &'static str;

/// Create a const [RuntimeString].
#[cfg(feature = "std")]
#[macro_export]
macro_rules! create_runtime_str {
	( $y:expr ) => {{ ::std::borrow::Cow::Borrowed($y) }}
}

/// Create a const [RuntimeString].
#[cfg(not(feature = "std"))]
#[macro_export]
macro_rules! create_runtime_str {
	( $y:expr ) => {{ $y }}
}

#[cfg(feature = "std")]
pub use serde::{Serialize, Deserialize, de::DeserializeOwned};

/// Complex storage builder stuff.
#[cfg(feature = "std")]
pub trait BuildStorage: Sized {
	/// Build the storage out of this builder.
	fn build_storage(self) -> Result<(StorageOverlay, ChildrenStorageOverlay), String> {
		let mut storage = Default::default();
		let mut child_storage = Default::default();
		self.assimilate_storage(&mut storage, &mut child_storage)?;
		Ok((storage, child_storage))
	}
	/// Assimilate the storage for this module into pre-existing overlays.
	fn assimilate_storage(
		self,
		storage: &mut StorageOverlay,
		child_storage: &mut ChildrenStorageOverlay
	) -> Result<(), String>;
}

/// Something that can build the genesis storage of a module.
#[cfg(feature = "std")]
pub trait BuildModuleGenesisStorage<T, I>: Sized {
	/// Create the module genesis storage into the given `storage` and `child_storage`.
	fn build_module_genesis_storage(
		self,
		storage: &mut StorageOverlay,
		child_storage: &mut ChildrenStorageOverlay
	) -> Result<(), String>;
}

#[cfg(feature = "std")]
impl BuildStorage for StorageOverlay {
	fn build_storage(self) -> Result<(StorageOverlay, ChildrenStorageOverlay), String> {
		Ok((self, Default::default()))
	}
	fn assimilate_storage(
		self,
		storage: &mut StorageOverlay,
		_child_storage: &mut ChildrenStorageOverlay
	) -> Result<(), String> {
		storage.extend(self);
		Ok(())
	}
}

#[cfg(feature = "std")]
impl BuildStorage for (StorageOverlay, ChildrenStorageOverlay) {
	fn build_storage(self) -> Result<(StorageOverlay, ChildrenStorageOverlay), String> {
		Ok(self)
	}
	fn assimilate_storage(
		self,
		storage: &mut StorageOverlay,
		child_storage: &mut ChildrenStorageOverlay
	)-> Result<(), String> {
		storage.extend(self.0);
		child_storage.extend(self.1);
		Ok(())
	}
}

/// Consensus engine unique ID.
pub type ConsensusEngineId = [u8; 4];


/// A fixed point number by the scale of 1 billion.
///
/// cannot hold a value larger than +-`9223372036854775807 / 1_000_000_000` (~9 billion).
#[cfg_attr(feature = "std", derive(Debug))]
#[derive(Encode, Decode, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Fixed64(i64);

/// The maximum value of the `Fixed64` type
const DIV: i64 = 1_000_000_000;

impl Fixed64 {
	/// creates self from a natural number.
	///
	/// Note that this might be lossy.
	pub fn from_natural(int: i64) -> Self {
		Self(int.saturating_mul(DIV))
	}

	/// Return the accuracy of the type. Given that this function returns the value `X`, it means
	/// that an instance composed of `X` parts (`Fixed64::from_parts(X)`) is equal to `1`.
	pub fn accuracy() -> i64 {
		DIV
	}

	/// creates self from a rational number. Equal to `n/d`.
	///
	/// Note that this might be lossy.
	pub fn from_rational(n: i64, d: u64) -> Self {
		Self((n as i128 * DIV as i128 / (d as i128).max(1)).try_into().unwrap_or(Bounded::max_value()))
	}

	/// Performs a saturated multiply and accumulate.
	///
	/// Returns a saturated `n + (self * n)`.
	/// TODO: generalize this to any weight type. #3189
	pub fn saturated_multiply_accumulate(&self, int: u32) -> u32 {
		let parts = self.0;
		let positive = parts > 0;

		// natural parts might overflow.
		let natural_parts = self.clone().saturated_into::<u32>();
		// fractional parts can always fit into u32.
		let perbill_parts = (parts.abs() % DIV) as u32;

		let n = int.saturating_mul(natural_parts);
		let p = Perbill::from_parts(perbill_parts) * int;
		// everything that needs to be either added or subtracted from the original weight.
		let excess = n.saturating_add(p);

		if positive {
			int.saturating_add(excess)
		} else {
			int.saturating_sub(excess)
		}
	}

	/// Raw constructor. Equal to `parts / 1_000_000_000`.
	pub fn from_parts(parts: i64) -> Self {
		Self(parts)
	}
}

impl UniqueSaturatedInto<u32> for Fixed64 {
	/// Note that the maximum value of Fixed64 might be more than what can fit in u32. This is hence,
	/// expected to be lossy.
	fn unique_saturated_into(self) -> u32 {
		(self.0.abs() / DIV).try_into().unwrap_or(Bounded::max_value())
	}
}

impl Saturating for Fixed64 {
	fn saturating_add(self, rhs: Self) -> Self {
		Self(self.0.saturating_add(rhs.0))
	}
	fn saturating_mul(self, rhs: Self) -> Self {
		Self(self.0.saturating_mul(rhs.0) / DIV)
	}
	fn saturating_sub(self, rhs: Self) -> Self {
		Self(self.0.saturating_sub(rhs.0))
	}
}

/// Note that this is a standard, _potentially-panicking_, implementation. Use `Saturating` trait
/// for safe addition.
impl ops::Add for Fixed64 {
	type Output = Self;

	fn add(self, rhs: Self) -> Self::Output {
		Self(self.0 + rhs.0)
	}
}

/// Note that this is a standard, _potentially-panicking_, implementation. Use `Saturating` trait
/// for safe subtraction.
impl ops::Sub for Fixed64 {
	type Output = Self;

	fn sub(self, rhs: Self) -> Self::Output {
		Self(self.0 - rhs.0)
	}
}

impl CheckedSub for Fixed64 {
	fn checked_sub(&self, rhs: &Self) -> Option<Self> {
		if let Some(v) = self.0.checked_sub(rhs.0) {
			Some(Self(v))
		} else {
			None
		}
	}
}

impl CheckedAdd for Fixed64 {
	fn checked_add(&self, rhs: &Self) -> Option<Self> {
		if let Some(v) = self.0.checked_add(rhs.0) {
			Some(Self(v))
		} else {
			None
		}
	}
}

/// PerU128 is parts-per-u128-max-value. It stores a value between 0 and 1 in fixed point.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[derive(Encode, Decode, Default, Copy, Clone, PartialEq, Eq)]
pub struct PerU128(u128);

const U128: u128 = u128::max_value();

impl PerU128 {
	/// Nothing.
	pub fn zero() -> Self { Self(0) }

	/// `true` if this is nothing.
	pub fn is_zero(&self) -> bool { self.0 == 0 }

	/// Everything.
	pub fn one() -> Self { Self(U128) }

	/// From an explicitly defined number of parts per maximum of the type.
	pub fn from_parts(x: u128) -> Self { Self(x) }

	/// Construct new instance where `x` is denominator and the nominator is 1.
	pub fn from_xth(x: u128) -> Self { Self(U128/x.max(1)) }
}

impl ::rstd::ops::Deref for PerU128 {
	type Target = u128;

	fn deref(&self) -> &u128 {
		&self.0
	}
}

impl codec::CompactAs for PerU128 {
	type As = u128;
	fn encode_as(&self) -> &u128 {
		&self.0
	}
	fn decode_from(x: u128) -> PerU128 {
		Self(x)
	}
}

impl From<codec::Compact<PerU128>> for PerU128 {
	fn from(x: codec::Compact<PerU128>) -> PerU128 {
		x.0
	}
}

/// Signature verify that can work with any known signature types..
#[derive(Eq, PartialEq, Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum MultiSignature {
	/// An Ed25519 signature.
	Ed25519(ed25519::Signature),
	/// An Sr25519 signature.
	Sr25519(sr25519::Signature),
}

impl From<ed25519::Signature> for MultiSignature {
	fn from(x: ed25519::Signature) -> Self {
		MultiSignature::Ed25519(x)
	}
}

impl From<sr25519::Signature> for MultiSignature {
	fn from(x: sr25519::Signature) -> Self {
		MultiSignature::Sr25519(x)
	}
}

impl Default for MultiSignature {
	fn default() -> Self {
		MultiSignature::Ed25519(Default::default())
	}
}

/// Public key for any known crypto algorithm.
#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub enum MultiSigner {
	/// An Ed25519 identity.
	Ed25519(ed25519::Public),
	/// An Sr25519 identity.
	Sr25519(sr25519::Public),
}

impl Default for MultiSigner {
	fn default() -> Self {
		MultiSigner::Ed25519(Default::default())
	}
}

/// NOTE: This implementations is required by `SimpleAddressDeterminator`,
/// we convert the hash into some AccountId, it's fine to use any scheme.
impl<T: Into<H256>> crypto::UncheckedFrom<T> for MultiSigner {
	fn unchecked_from(x: T) -> Self {
		ed25519::Public::unchecked_from(x.into()).into()
	}
}

impl AsRef<[u8]> for MultiSigner {
	fn as_ref(&self) -> &[u8] {
		match *self {
			MultiSigner::Ed25519(ref who) => who.as_ref(),
			MultiSigner::Sr25519(ref who) => who.as_ref(),
		}
	}
}

impl From<ed25519::Public> for MultiSigner {
	fn from(x: ed25519::Public) -> Self {
		MultiSigner::Ed25519(x)
	}
}

impl From<sr25519::Public> for MultiSigner {
	fn from(x: sr25519::Public) -> Self {
		MultiSigner::Sr25519(x)
	}
}

 #[cfg(feature = "std")]
impl std::fmt::Display for MultiSigner {
	fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
		match *self {
			MultiSigner::Ed25519(ref who) => write!(fmt, "ed25519: {}", who),
			MultiSigner::Sr25519(ref who) => write!(fmt, "sr25519: {}", who),
		}
	}
}

impl Verify for MultiSignature {
	type Signer = MultiSigner;
	fn verify<L: Lazy<[u8]>>(&self, msg: L, signer: &Self::Signer) -> bool {
		match (self, signer) {
			(MultiSignature::Ed25519(ref sig), &MultiSigner::Ed25519(ref who)) => sig.verify(msg, who),
			(MultiSignature::Sr25519(ref sig), &MultiSigner::Sr25519(ref who)) => sig.verify(msg, who),
			_ => false,
		}
	}
}

/// Signature verify that can work with any known signature types..
#[derive(Eq, PartialEq, Clone, Default, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct AnySignature(H512);

impl Verify for AnySignature {
	type Signer = sr25519::Public;
	fn verify<L: Lazy<[u8]>>(&self, mut msg: L, signer: &sr25519::Public) -> bool {
		runtime_io::sr25519_verify(self.0.as_fixed_bytes(), msg.get(), &signer.0) ||
			runtime_io::ed25519_verify(self.0.as_fixed_bytes(), msg.get(), &signer.0)
	}
}

impl From<sr25519::Signature> for AnySignature {
	fn from(s: sr25519::Signature) -> Self {
		AnySignature(s.into())
	}
}

impl From<ed25519::Signature> for AnySignature {
	fn from(s: ed25519::Signature) -> Self {
		AnySignature(s.into())
	}
}

#[derive(Eq, PartialEq, Clone, Copy, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Serialize))]
#[repr(u8)]
/// Outcome of a valid extrinsic application. Capable of being sliced.
pub enum ApplyOutcome {
	/// Successful application (extrinsic reported no issue).
	Success = 0,
	/// Failed application (extrinsic was probably a no-op other than fees).
	Fail = 1,
}

impl codec::Encode for ApplyOutcome {
	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(&[*self as u8])
	}
}

#[derive(Eq, PartialEq, Clone, Copy, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Serialize))]
#[repr(u8)]
/// Reason why an extrinsic couldn't be applied (i.e. invalid extrinsic).
pub enum ApplyError {
	/// Bad signature.
	BadSignature = 0,
	/// Nonce too low.
	Stale = 1,
	/// Nonce too high.
	Future = 2,
	/// Sending account had too low a balance.
	CantPay = 3,
	/// Block is full, no more extrinsics can be applied.
	FullBlock = 255,
}

impl codec::Encode for ApplyError {
	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(&[*self as u8])
	}
}

/// Result from attempt to apply an extrinsic.
pub type ApplyResult = Result<ApplyOutcome, ApplyError>;

/// Verify a signature on an encoded value in a lazy manner. This can be
/// an optimization if the signature scheme has an "unsigned" escape hash.
pub fn verify_encoded_lazy<V: Verify, T: codec::Encode>(sig: &V, item: &T, signer: &V::Signer) -> bool {
	// The `Lazy<T>` trait expresses something like `X: FnMut<Output = for<'a> &'a T>`.
	// unfortunately this is a lifetime relationship that can't
	// be expressed without generic associated types, better unification of HRTBs in type position,
	// and some kind of integration into the Fn* traits.
	struct LazyEncode<F> {
		inner: F,
		encoded: Option<Vec<u8>>,
	}

	impl<F: Fn() -> Vec<u8>> traits::Lazy<[u8]> for LazyEncode<F> {
		fn get(&mut self) -> &[u8] {
			self.encoded.get_or_insert_with(&self.inner).as_slice()
		}
	}

	sig.verify(
		LazyEncode { inner: || item.encode(), encoded: None },
		signer,
	)
}

/// Helper macro for `impl_outer_config`
#[macro_export]
macro_rules! __impl_outer_config_types {
	// Generic + Instance
	(
		$concrete:ident $config:ident $snake:ident { $instance:ident } < $ignore:ident >;
		$( $rest:tt )*
	) => {
		#[cfg(any(feature = "std", test))]
		pub type $config = $snake::GenesisConfig<$concrete, $snake::$instance>;
		$crate::__impl_outer_config_types! { $concrete $( $rest )* }
	};
	// Generic
	(
		$concrete:ident $config:ident $snake:ident < $ignore:ident >;
		$( $rest:tt )*
	) => {
		#[cfg(any(feature = "std", test))]
		pub type $config = $snake::GenesisConfig<$concrete>;
		$crate::__impl_outer_config_types! { $concrete $( $rest )* }
	};
	// No Generic and maybe Instance
	(
		$concrete:ident $config:ident $snake:ident $( { $instance:ident } )?;
		$( $rest:tt )*
	) => {
		#[cfg(any(feature = "std", test))]
		pub type $config = $snake::GenesisConfig;
		$crate::__impl_outer_config_types! { $concrete $( $rest )* }
	};
	($concrete:ident) => ()
}

/// Implement the output "meta" module configuration struct,
/// which is basically:
/// pub struct GenesisConfig {
/// 	rust_module_one: Option<ModuleOneConfig>,
/// 	...
/// }
#[macro_export]
macro_rules! impl_outer_config {
	(
		pub struct $main:ident for $concrete:ident {
			$( $config:ident =>
				$snake:ident $( $instance:ident )? $( <$generic:ident> )*, )*
		}
	) => {
		$crate::__impl_outer_config_types! {
			$concrete $( $config $snake $( { $instance } )? $( <$generic> )*; )*
		}

		$crate::paste::item! {
			#[cfg(any(feature = "std", test))]
			#[derive($crate::serde::Serialize, $crate::serde::Deserialize)]
			#[serde(rename_all = "camelCase")]
			#[serde(deny_unknown_fields)]
			pub struct $main {
				$(
					pub [< $snake $(_ $instance )? >]: Option<$config>,
				)*
			}
			#[cfg(any(feature = "std", test))]
			impl $crate::BuildStorage for $main {
				fn assimilate_storage(
					self,
					top: &mut $crate::StorageOverlay,
					children: &mut $crate::ChildrenStorageOverlay
				) -> std::result::Result<(), String> {
					$(
						if let Some(extra) = self.[< $snake $(_ $instance )? >] {
							$crate::impl_outer_config! {
								@CALL_FN
								$concrete;
								$snake;
								$( $instance )?;
								extra;
								top;
								children;
							}
						}
					)*
					Ok(())
				}
			}
		}
	};
	(@CALL_FN
		$runtime:ident;
		$module:ident;
		$instance:ident;
		$extra:ident;
		$top:ident;
		$children:ident;
	) => {
		$crate::BuildModuleGenesisStorage::<$runtime, $module::$instance>::build_module_genesis_storage(
			$extra,
			$top,
			$children,
		)?;
	};
	(@CALL_FN
		$runtime:ident;
		$module:ident;
		;
		$extra:ident;
		$top:ident;
		$children:ident;
	) => {
		$crate::BuildModuleGenesisStorage::<$runtime, $module::__InherentHiddenInstance>::build_module_genesis_storage(
			$extra,
			$top,
			$children,
		)?;
	}
}

/// Simple blob to hold an extrinsic without committing to its format and ensure it is serialized
/// correctly.
#[derive(PartialEq, Eq, Clone, Default, Encode, Decode)]
pub struct OpaqueExtrinsic(pub Vec<u8>);

#[cfg(feature = "std")]
impl std::fmt::Debug for OpaqueExtrinsic {
	fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(fmt, "{}", primitives::hexdisplay::HexDisplay::from(&self.0))
	}
}

#[cfg(feature = "std")]
impl ::serde::Serialize for OpaqueExtrinsic {
	fn serialize<S>(&self, seq: S) -> Result<S::Ok, S::Error> where S: ::serde::Serializer {
		codec::Encode::using_encoded(&self.0, |bytes| ::primitives::bytes::serialize(bytes, seq))
	}
}

impl traits::Extrinsic for OpaqueExtrinsic {
	type Call = ();

	fn is_signed(&self) -> Option<bool> {
		None
	}

	fn new_unsigned(_call: Self::Call) -> Option<Self> { None }
}

#[cfg(test)]
mod tests {
	#[test]
	fn opaque_extrinsic_serialization() {
		let ex = super::OpaqueExtrinsic(vec![1, 2, 3, 4]);
		assert_eq!(serde_json::to_string(&ex).unwrap(), "\"0x1001020304\"".to_owned());
	}
}
