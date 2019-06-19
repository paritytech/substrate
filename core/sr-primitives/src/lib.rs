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

#[cfg(feature = "std")]
pub use runtime_io::{StorageOverlay, ChildrenStorageOverlay};

use rstd::{prelude::*, ops};
use substrate_primitives::{crypto, ed25519, sr25519, hash::{H256, H512}};
use codec::{Encode, Decode};

#[cfg(feature = "std")]
pub mod testing;

pub mod weights;
pub mod traits;
use traits::{SaturatedConversion, UniqueSaturatedInto};

pub mod generic;
pub mod transaction_validity;

/// Re-export these since they're only "kind of" generic.
pub use generic::{DigestItem, Digest};

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
	fn assimilate_storage(self, storage: &mut StorageOverlay, child_storage: &mut ChildrenStorageOverlay) -> Result<(), String>;
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

/// Permill is parts-per-million (i.e. after multiplying by this, divide by 1000000).
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[derive(Encode, Decode, Default, Copy, Clone, PartialEq, Eq)]
pub struct Permill(u32);

impl Permill {
	/// Nothing.
	pub fn zero() -> Self { Self(0) }

	/// `true` if this is nothing.
	pub fn is_zero(&self) -> bool { self.0 == 0 }

	/// Everything.
	pub fn one() -> Self { Self(1_000_000) }

	/// From an explicitly defined number of parts per maximum of the type.
	pub fn from_parts(x: u32) -> Self { Self(x.min(1_000_000)) }

	/// Converts from a percent. Equal to `x / 100`.
	pub fn from_percent(x: u32) -> Self { Self(x.min(100) * 10_000) }

	/// Converts a fraction into `Permill`.
	#[cfg(feature = "std")]
	pub fn from_fraction(x: f64) -> Self { Self((x * 1_000_000.0) as u32) }
}

impl<N> ops::Mul<N> for Permill
where
	N: Clone + From<u32> + UniqueSaturatedInto<u32> + ops::Rem<N, Output=N>
		+ ops::Div<N, Output=N> + ops::Mul<N, Output=N> + ops::Add<N, Output=N>,
{
	type Output = N;
	fn mul(self, b: N) -> Self::Output {
		let million: N = 1_000_000.into();
		let part: N = self.0.into();

		let rem_multiplied_divided = {
			let rem = b.clone().rem(million.clone());

			// `rem` is inferior to one million, thus it fits into u32
			let rem_u32 = rem.saturated_into::<u32>();

			// `self` and `rem` are inferior to one million, thus the product is less than 10^12
			// and fits into u64
			let rem_multiplied_u64 = rem_u32 as u64 * self.0 as u64;

			// `rem_multiplied_u64` is less than 10^12 therefore divided by a million it fits into
			// u32
			let rem_multiplied_divided_u32 = (rem_multiplied_u64 / 1_000_000) as u32;

			// `rem_multiplied_divided` is inferior to b, thus it can be converted back to N type
			rem_multiplied_divided_u32.into()
		};

		(b / million) * part + rem_multiplied_divided
	}
}

#[cfg(feature = "std")]
impl From<f64> for Permill {
	fn from(x: f64) -> Permill {
		Permill::from_fraction(x)
	}
}

#[cfg(feature = "std")]
impl From<f32> for Permill {
	fn from(x: f32) -> Permill {
		Permill::from_fraction(x as f64)
	}
}

impl codec::CompactAs for Permill {
	type As = u32;
	fn encode_as(&self) -> &u32 {
		&self.0
	}
	fn decode_from(x: u32) -> Permill {
		Permill(x)
	}
}

impl From<codec::Compact<Permill>> for Permill {
	fn from(x: codec::Compact<Permill>) -> Permill {
		x.0
	}
}

/// Perbill is parts-per-billion. It stores a value between 0 and 1 in fixed point and
/// provides a means to multiply some other value by that.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[derive(Encode, Decode, Default, Copy, Clone, PartialEq, Eq)]
pub struct Perbill(u32);

impl Perbill {
	/// Nothing.
	pub fn zero() -> Self { Self(0) }

	/// `true` if this is nothing.
	pub fn is_zero(&self) -> bool { self.0 == 0 }

	/// Everything.
	pub fn one() -> Self { Self(1_000_000_000) }

	/// From an explicitly defined number of parts per maximum of the type.
	pub fn from_parts(x: u32) -> Self { Self(x.min(1_000_000_000)) }

	/// Converts from a percent. Equal to `x / 100`.
	pub fn from_percent(x: u32) -> Self { Self(x.min(100) * 10_000_000) }

	/// Construct new instance where `x` is in millionths. Value equivalent to `x / 1,000,000`.
	pub fn from_millionths(x: u32) -> Self { Self(x.min(1_000_000) * 1000) }

	#[cfg(feature = "std")]
	/// Construct new instance whose value is equal to `x` (between 0 and 1).
	pub fn from_fraction(x: f64) -> Self { Self((x.max(0.0).min(1.0) * 1_000_000_000.0) as u32) }
}

impl<N> ops::Mul<N> for Perbill
where
	N: Clone + From<u32> + UniqueSaturatedInto<u32> + ops::Rem<N, Output=N>
	+ ops::Div<N, Output=N> + ops::Mul<N, Output=N> + ops::Add<N, Output=N>,
{
	type Output = N;
	fn mul(self, b: N) -> Self::Output {
		let billion: N = 1_000_000_000.into();
		let part: N = self.0.into();

		let rem_multiplied_divided = {
			let rem = b.clone().rem(billion.clone());

			// `rem` is inferior to one billion, thus it fits into u32
			let rem_u32 = rem.saturated_into::<u32>();

			// `self` and `rem` are inferior to one billion, thus the product is less than 10^18
			// and fits into u64
			let rem_multiplied_u64 = rem_u32 as u64 * self.0 as u64;

			// `rem_multiplied_u64` is less than 10^18 therefore divided by a billion it fits into
			// u32
			let rem_multiplied_divided_u32 = (rem_multiplied_u64 / 1_000_000_000) as u32;

			// `rem_multiplied_divided` is inferior to b, thus it can be converted back to N type
			rem_multiplied_divided_u32.into()
		};

		(b / billion) * part + rem_multiplied_divided
	}
}

#[cfg(feature = "std")]
impl From<f64> for Perbill {
	fn from(x: f64) -> Perbill {
		Perbill::from_fraction(x)
	}
}

#[cfg(feature = "std")]
impl From<f32> for Perbill {
	fn from(x: f32) -> Perbill {
		Perbill::from_fraction(x as f64)
	}
}

impl codec::CompactAs for Perbill {
	type As = u32;
	fn encode_as(&self) -> &u32 {
		&self.0
	}
	fn decode_from(x: u32) -> Perbill {
		Perbill(x)
	}
}

impl From<codec::Compact<Perbill>> for Perbill {
	fn from(x: codec::Compact<Perbill>) -> Perbill {
		x.0
	}
}

/// PerU128 is parts-per-u128-max-value. It stores a value between 0 and 1 in fixed point and
/// provides a means to multiply some other value by that.
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
	(
		$concrete:ident $config:ident $snake:ident < $ignore:ident, $instance:path > $( $rest:tt )*
	) => {
		#[cfg(any(feature = "std", test))]
		pub type $config = $snake::GenesisConfig<$concrete, $instance>;
		$crate::__impl_outer_config_types! {$concrete $($rest)*}
	};
	(
		$concrete:ident $config:ident $snake:ident < $ignore:ident > $( $rest:tt )*
	) => {
		#[cfg(any(feature = "std", test))]
		pub type $config = $snake::GenesisConfig<$concrete>;
		$crate::__impl_outer_config_types! {$concrete $($rest)*}
	};
	(
		$concrete:ident $config:ident $snake:ident $( $rest:tt )*
	) => {
		#[cfg(any(feature = "std", test))]
		pub type $config = $snake::GenesisConfig;
		__impl_outer_config_types! {$concrete $($rest)*}
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
			$( $config:ident => $snake:ident $( < $generic:ident $(, $instance:path)? > )*, )*
		}
	) => {
		$crate::__impl_outer_config_types! { $concrete $( $config $snake $( < $generic $(, $instance)? > )* )* }
		#[cfg(any(feature = "std", test))]
		#[derive($crate::serde::Serialize, $crate::serde::Deserialize)]
		#[serde(rename_all = "camelCase")]
		#[serde(deny_unknown_fields)]
		pub struct $main {
			$(
				pub $snake: Option<$config>,
			)*
		}
		#[cfg(any(feature = "std", test))]
		impl $crate::BuildStorage for $main {
			fn assimilate_storage(self, top: &mut $crate::StorageOverlay, children: &mut $crate::ChildrenStorageOverlay) -> ::std::result::Result<(), String> {
				$(
					if let Some(extra) = self.$snake {
						extra.assimilate_storage(top, children)?;
					}
				)*
				Ok(())
			}
		}
	}
}

/// Simple blob to hold an extrinsic without committing to its format and ensure it is serialized
/// correctly.
#[derive(PartialEq, Eq, Clone, Default, Encode, Decode)]
pub struct OpaqueExtrinsic(pub Vec<u8>);

#[cfg(feature = "std")]
impl std::fmt::Debug for OpaqueExtrinsic {
	fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(fmt, "{}", substrate_primitives::hexdisplay::HexDisplay::from(&self.0))
	}
}

#[cfg(feature = "std")]
impl ::serde::Serialize for OpaqueExtrinsic {
	fn serialize<S>(&self, seq: S) -> Result<S::Ok, S::Error> where S: ::serde::Serializer {
		codec::Encode::using_encoded(&self.0, |bytes| ::substrate_primitives::bytes::serialize(bytes, seq))
	}
}

impl traits::Extrinsic for OpaqueExtrinsic {
	fn is_signed(&self) -> Option<bool> {
		None
	}
}

#[cfg(test)]
mod tests {
	use crate::codec::{Encode, Decode};

	macro_rules! per_thing_mul_upper_test {
		($num_type:tt, $per:tt) => {
			// all sort of from_percent
			assert_eq!($per::from_percent(100) * $num_type::max_value(), $num_type::max_value());
			assert_eq!(
				$per::from_percent(99) * $num_type::max_value(),
				((Into::<U256>::into($num_type::max_value()) * 99u32) / 100u32).as_u128() as $num_type
			);
			assert_eq!($per::from_percent(50) * $num_type::max_value(), $num_type::max_value() / 2);
			assert_eq!($per::from_percent(1) * $num_type::max_value(), $num_type::max_value() / 100);
			assert_eq!($per::from_percent(0) * $num_type::max_value(), 0);

			// bounds
			assert_eq!($per::one() * $num_type::max_value(), $num_type::max_value());
			assert_eq!($per::zero() * $num_type::max_value(), 0);
		}
	}

	#[test]
	fn opaque_extrinsic_serialization() {
		let ex = super::OpaqueExtrinsic(vec![1, 2, 3, 4]);
		assert_eq!(serde_json::to_string(&ex).unwrap(), "\"0x1001020304\"".to_owned());
	}

	#[test]
	fn compact_permill_perbill_encoding() {
		let tests = [(0u32, 1usize), (63, 1), (64, 2), (16383, 2), (16384, 4), (1073741823, 4), (1073741824, 5), (u32::max_value(), 5)];
		for &(n, l) in &tests {
			let compact: crate::codec::Compact<super::Permill> = super::Permill(n).into();
			let encoded = compact.encode();
			assert_eq!(encoded.len(), l);
			let decoded = <crate::codec::Compact<super::Permill>>::decode(&mut & encoded[..]).unwrap();
			let permill: super::Permill = decoded.into();
			assert_eq!(permill, super::Permill(n));

			let compact: crate::codec::Compact<super::Perbill> = super::Perbill(n).into();
			let encoded = compact.encode();
			assert_eq!(encoded.len(), l);
			let decoded = <crate::codec::Compact<super::Perbill>>::decode(&mut & encoded[..]).unwrap();
			let perbill: super::Perbill = decoded.into();
			assert_eq!(perbill, super::Perbill(n));
		}
	}

	#[derive(Encode, Decode, PartialEq, Eq, Debug)]
	struct WithCompact<T: crate::codec::HasCompact> {
		data: T,
	}

	#[test]
	fn test_has_compact_permill() {
		let data = WithCompact { data: super::Permill(1) };
		let encoded = data.encode();
		assert_eq!(data, WithCompact::<super::Permill>::decode(&mut &encoded[..]).unwrap());
	}

	#[test]
	fn test_has_compact_perbill() {
		let data = WithCompact { data: super::Perbill(1) };
		let encoded = data.encode();
		assert_eq!(data, WithCompact::<super::Perbill>::decode(&mut &encoded[..]).unwrap());
	}

	#[test]
	fn per_things_should_work() {
		use super::{Perbill, Permill};
		use primitive_types::U256;

		per_thing_mul_upper_test!(u32, Perbill);
		per_thing_mul_upper_test!(u64, Perbill);
		per_thing_mul_upper_test!(u128, Perbill);

		per_thing_mul_upper_test!(u32, Permill);
		per_thing_mul_upper_test!(u64, Permill);
		per_thing_mul_upper_test!(u128, Permill);
	}

	#[test]
	fn per_things_operate_in_output_type() {
		assert_eq!(super::Perbill::one() * 255_u64, 255);
	}

	#[test]
	fn per_things_one_minus_one_part() {
		use primitive_types::U256;

		assert_eq!(
			super::Perbill::from_parts(999_999_999) * std::u128::MAX,
			((Into::<U256>::into(std::u128::MAX) * 999_999_999u32) / 1_000_000_000u32).as_u128()
		);

		assert_eq!(
			super::Permill::from_parts(999_999) * std::u128::MAX,
			((Into::<U256>::into(std::u128::MAX) * 999_999u32) / 1_000_000u32).as_u128()
		);
	}
}
