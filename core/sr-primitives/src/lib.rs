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

//! System manager: Handles all of the top-level stuff; executing block/transaction, setting code
//! and depositing logs.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
extern crate serde;

#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;

#[cfg(feature = "std")]
#[macro_use]
extern crate log;

#[macro_use]
extern crate parity_codec_derive;

extern crate num_traits;
extern crate integer_sqrt;
extern crate sr_std as rstd;
extern crate sr_io as runtime_io;
#[doc(hidden)]
pub extern crate parity_codec as codec;
extern crate substrate_primitives;

#[cfg(test)]
extern crate serde_json;

#[cfg(feature = "std")]
use std::collections::HashMap;

use rstd::prelude::*;
use substrate_primitives::hash::{H256, H512};

#[cfg(feature = "std")]
use substrate_primitives::hexdisplay::ascii_format;

#[cfg(feature = "std")]
pub mod testing;

pub mod traits;
pub mod generic;
pub mod transaction_validity;

pub type Justification = Vec<u8>;

use traits::{Verify, Lazy};

/// A String that is a `&'static str` on `no_std` and a `String` on `std`.
#[cfg(not(feature = "std"))]
pub type RuntimeString = &'static str;
#[cfg(feature = "std")]
pub type RuntimeString = ::std::borrow::Cow<'static, str>;

#[cfg(feature = "std")]
pub use serde::{Serialize, de::DeserializeOwned};

/// A set of key value pairs for storage.
#[cfg(feature = "std")]
pub type StorageMap = HashMap<Vec<u8>, Vec<u8>>;

/// A set of key value pairs for children storage;
#[cfg(feature = "std")]
pub type ChildrenStorageMap = HashMap<Vec<u8>, StorageMap>;

/// Complex storage builder stuff.
#[cfg(feature = "std")]
pub trait BuildStorage {
	fn hash(data: &[u8]) -> [u8; 16] {
		let r = runtime_io::twox_128(data);
		trace!(target: "build_storage", "{} <= {}", substrate_primitives::hexdisplay::HexDisplay::from(&r), ascii_format(data));
		r
	}
	fn build_storage(self) -> Result<(StorageMap, ChildrenStorageMap), String>;
}

#[cfg(feature = "std")]
impl BuildStorage for StorageMap {
	fn build_storage(self) -> Result<(StorageMap, ChildrenStorageMap), String> {
		Ok((self, Default::default()))
	}
}

/// Permill is parts-per-million (i.e. after multiplying by this, divide by 1000000).
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[derive(Encode, Decode, Default, Copy, Clone, PartialEq, Eq)]
pub struct Permill(u32);

// TODO: impl Mul<Permill> for N where N: As<usize>
impl Permill {
	pub fn times<N: traits::As<u64> + ::rstd::ops::Mul<N, Output=N> + ::rstd::ops::Div<N, Output=N>>(self, b: N) -> N {
		// TODO: handle overflows
		b * <N as traits::As<u64>>::sa(self.0 as u64) / <N as traits::As<u64>>::sa(1000000)
	}

	pub fn from_millionths(x: u32) -> Permill { Permill(x) }

	pub fn from_percent(x: u32) -> Permill { Permill(x * 10_000) }

	#[cfg(feature = "std")]
	pub fn from_fraction(x: f64) -> Permill { Permill((x * 1_000_000.0) as u32) }
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

/// Perbill is parts-per-billion. It stores a value between 0 and 1 in fixed point and
/// provides a means to multiply some other value by that.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[derive(Encode, Decode, Default, Copy, Clone, PartialEq, Eq)]
pub struct Perbill(u32);

// TODO: impl Mul<Perbill> for N where N: As<usize>
impl Perbill {
	/// Attenuate `b` by self.
	pub fn times<N: traits::As<u64> + ::rstd::ops::Mul<N, Output=N> + ::rstd::ops::Div<N, Output=N>>(self, b: N) -> N {
		// TODO: handle overflows
		b * <N as traits::As<u64>>::sa(self.0 as u64) / <N as traits::As<u64>>::sa(1_000_000_000)
	}

	/// Nothing.
	pub fn zero() -> Perbill { Perbill(0) }

	/// `true` if this is nothing.
	pub fn is_zero(&self) -> bool { self.0 == 0 }

	/// Everything.
	pub fn one() -> Perbill { Perbill(1_000_000_000) }

	/// Construct new instance where `x` is in billionths. Value equivalent to `x / 1,000,000,000`.
	pub fn from_billionths(x: u32) -> Perbill { Perbill(x.min(1_000_000_000)) }

	/// Construct new instance where `x` is in millionths. Value equivalent to `x / 1,000,000`.
	pub fn from_millionths(x: u32) -> Perbill { Perbill(x.min(1_000_000) * 1000) }

	/// Construct new instance where `x` is a percent. Value equivalent to `x%`.
	pub fn from_percent(x: u32) -> Perbill { Perbill(x.min(100) * 10_000_000) }

	#[cfg(feature = "std")]
	/// Construct new instance whose value is equal to `x` (between 0 and 1).
	pub fn from_fraction(x: f64) -> Perbill { Perbill((x.max(0.0).min(1.0) * 1_000_000_000.0) as u32) }

	#[cfg(feature = "std")]
	/// Construct new instance whose value is equal to `n / d` (between 0 and 1).
	pub fn from_rational(n: f64, d: f64) -> Perbill { Perbill(((n / d).max(0.0).min(1.0) * 1_000_000_000.0) as u32) }
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

/// Ed25519 signature verify.
#[derive(Eq, PartialEq, Clone, Default, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct Ed25519Signature(pub H512);

impl Verify for Ed25519Signature {
	type Signer = H256;
	fn verify<L: Lazy<[u8]>>(&self, mut msg: L, signer: &Self::Signer) -> bool {
		runtime_io::ed25519_verify((self.0).as_fixed_bytes(), msg.get(), &signer.as_bytes())
	}
}

impl From<H512> for Ed25519Signature {
	fn from(h: H512) -> Ed25519Signature {
		Ed25519Signature(h)
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

#[macro_export]
macro_rules! __impl_outer_config_types {
	(
		$concrete:ident $config:ident $snake:ident < $ignore:ident > $( $rest:tt )*
	) => {
		#[cfg(any(feature = "std", test))]
		pub type $config = $snake::GenesisConfig<$concrete>;
		__impl_outer_config_types! {$concrete $($rest)*}
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

#[macro_export]
/// Implement the output "meta" module configuration struct.
macro_rules! impl_outer_config {
	(
		pub struct $main:ident for $concrete:ident {
			$( $config:ident => $snake:ident $( < $generic:ident > )*, )*
		}
	) => {
		__impl_outer_config_types! { $concrete $( $config $snake $( < $generic > )* )* }
		#[cfg(any(feature = "std", test))]
		#[derive(Serialize, Deserialize)]
		#[serde(rename_all = "camelCase")]
		#[serde(deny_unknown_fields)]
		pub struct $main {
			$(
				pub $snake: Option<$config>,
			)*
		}
		#[cfg(any(feature = "std", test))]
		impl $crate::BuildStorage for $main {
			fn build_storage(self) -> ::std::result::Result<($crate::StorageMap, $crate::ChildrenStorageMap), String> {
				let mut top = $crate::StorageMap::new();
				let mut children = $crate::ChildrenStorageMap::new();
				$(
					if let Some(extra) = self.$snake {
						let (other_top, other_children) = extra.build_storage()?;
						top.extend(other_top);
						for (other_child_key, other_child_map) in other_children {
							children.entry(other_child_key).or_default().extend(other_child_map);
						}
					}
				)*
				Ok((top, children))
			}
		}
	}
}

/// Generates enum that contains all possible log entries for the runtime.
/// Every individual module of the runtime that is mentioned, must
/// expose a `Log` and `RawLog` enums.
///
/// Generated enum is binary-compatible with and could be interpreted
/// as `generic::DigestItem`.
///
/// Runtime requirements:
/// 1) binary representation of all supported 'system' log items should stay
///    the same. Otherwise, the native code will be unable to read log items
///    generated by previous runtime versions
/// 2) the support of 'system' log items should never be dropped by runtime.
///    Otherwise, native code will lost its ability to read items of this type
///    even if they were generated by the versions which have supported these
///    items.
#[macro_export]
macro_rules! impl_outer_log {
	(
		$(#[$attr:meta])*
		pub enum $name:ident ($internal:ident: DigestItem<$( $genarg:ty ),*>) for $trait:ident {
			$( $module:ident( $( $sitem:ident ),* ) ),*
		}
	) => {
		/// Wrapper for all possible log entries for the `$trait` runtime. Provides binary-compatible
		/// `Encode`/`Decode` implementations with the corresponding `generic::DigestItem`.
		#[derive(Clone, PartialEq, Eq)]
		#[cfg_attr(feature = "std", derive(Debug, Serialize))]
		$(#[$attr])*
		#[allow(non_camel_case_types)]
		pub struct $name($internal);

		/// All possible log entries for the `$trait` runtime. `Encode`/`Decode` implementations
		/// are auto-generated => it is not binary-compatible with `generic::DigestItem`.
		#[derive(Clone, PartialEq, Eq, Encode, Decode)]
		#[cfg_attr(feature = "std", derive(Debug, Serialize))]
		$(#[$attr])*
		#[allow(non_camel_case_types)]
		pub enum InternalLog {
			$(
				$module($module::Log<$trait>),
			)*
		}

		impl $name {
			/// Try to convert `$name` into `generic::DigestItemRef`. Returns Some when
			/// `self` is a 'system' log && it has been marked as 'system' in macro call.
			/// Otherwise, None is returned.
			#[allow(unreachable_patterns)]
			fn dref<'a>(&'a self) -> Option<$crate::generic::DigestItemRef<'a, $($genarg),*>> {
				match self.0 {
					$($(
					$internal::$module($module::RawLog::$sitem(ref v)) =>
						Some($crate::generic::DigestItemRef::$sitem(v)),
					)*)*
					_ => None,
				}
			}
		}

		impl $crate::traits::DigestItem for $name {
			type Hash = <$crate::generic::DigestItem<$($genarg),*> as $crate::traits::DigestItem>::Hash;
			type AuthorityId = <$crate::generic::DigestItem<$($genarg),*> as $crate::traits::DigestItem>::AuthorityId;

			fn as_authorities_change(&self) -> Option<&[Self::AuthorityId]> {
				self.dref().and_then(|dref| dref.as_authorities_change())
			}

			fn as_changes_trie_root(&self) -> Option<&Self::Hash> {
				self.dref().and_then(|dref| dref.as_changes_trie_root())
			}
		}

		impl From<$crate::generic::DigestItem<$($genarg),*>> for $name {
			/// Converts `generic::DigestItem` into `$name`. If `generic::DigestItem` represents
			/// a system item which is supported by the runtime, it is returned.
			/// Otherwise we expect a `Other` log item. Trying to convert from anything other
			/// will lead to panic in runtime, since the runtime does not supports this 'system'
			/// log item.
			#[allow(unreachable_patterns)]
			fn from(gen: $crate::generic::DigestItem<$($genarg),*>) -> Self {
				match gen {
					$($(
					$crate::generic::DigestItem::$sitem(value) =>
						$name($internal::$module($module::RawLog::$sitem(value))),
					)*)*
					_ => gen.as_other()
						.and_then(|value| $crate::codec::Decode::decode(&mut &value[..]))
						.map($name)
						.expect("not allowed to fail in runtime"),
				}
			}
		}

		impl $crate::codec::Decode for $name {
			/// `generic::DigestItem` binray compatible decode.
			fn decode<I: $crate::codec::Input>(input: &mut I) -> Option<Self> {
				let gen: $crate::generic::DigestItem<$($genarg),*> =
					$crate::codec::Decode::decode(input)?;
				Some($name::from(gen))
			}
		}

		impl $crate::codec::Encode for $name {
			/// `generic::DigestItem` binray compatible encode.
			fn encode(&self) -> Vec<u8> {
				match self.dref() {
					Some(dref) => dref.encode(),
					None => {
						let gen: $crate::generic::DigestItem<$($genarg),*> =
							$crate::generic::DigestItem::Other(self.0.encode());
						gen.encode()
					},
				}
			}
		}

		$(
			impl From<$module::Log<$trait>> for $name {
				/// Converts single module log item into `$name`.
				fn from(x: $module::Log<$trait>) -> Self {
					$name(x.into())
				}
			}

			impl From<$module::Log<$trait>> for InternalLog {
				/// Converts single module log item into `$internal`.
				fn from(x: $module::Log<$trait>) -> Self {
					InternalLog::$module(x)
				}
			}
		)*
	};
}

//TODO: https://github.com/paritytech/substrate/issues/1022
/// Inherent data to include in a block.
#[derive(Encode, Decode)]
pub struct InherentData {
	/// Current timestamp.
	pub timestamp: u64,
	/// Indices of offline validators.
	pub offline_indices: Vec<u32>,
}

impl InherentData {
	/// Create a new `InherentData` instance.
	pub fn new(timestamp: u64, offline_indices: Vec<u32>) -> Self {
		Self {
			timestamp,
			offline_indices
		}
	}
}

//TODO: https://github.com/paritytech/substrate/issues/1022
/// Error type used while checking inherents.
#[derive(Encode, Decode)]
pub enum CheckInherentError {
	TimestampInFuture(u64),
	#[cfg(feature = "std")]
	Other(String),
	#[cfg(not(feature = "std"))]
	Other(&'static str),
}

#[cfg(test)]
mod tests {
	use substrate_primitives::hash::H256;
	use codec::{Encode as EncodeHidden, Decode as DecodeHidden};
	use traits::DigestItem;

	pub trait RuntimeT {
		type AuthorityId;
	}

	pub struct Runtime;

	impl RuntimeT for Runtime {
		type AuthorityId = u64;
	}

	mod a {
		use super::RuntimeT;
		pub type Log<R> = RawLog<<R as RuntimeT>::AuthorityId>;

		#[derive(Serialize, Debug, Encode, Decode, PartialEq, Eq, Clone)]
		pub enum RawLog<AuthorityId> { A1(AuthorityId), AuthoritiesChange(Vec<AuthorityId>), A3(AuthorityId) }
	}

	mod b {
		use super::RuntimeT;
		pub type Log<R> = RawLog<<R as RuntimeT>::AuthorityId>;

		#[derive(Serialize, Debug, Encode, Decode, PartialEq, Eq, Clone)]
		pub enum RawLog<AuthorityId> { B1(AuthorityId), B2(AuthorityId) }
	}

	// TODO try to avoid redundant brackets: a(AuthoritiesChange), b
	impl_outer_log! {
		pub enum Log(InternalLog: DigestItem<H256, u64>) for Runtime {
			a(AuthoritiesChange), b()
		}
	}

	#[test]
	fn impl_outer_log_works() {
		// encode/decode regular item
		let b1: Log = b::RawLog::B1::<u64>(777).into();
		let encoded_b1 = b1.encode();
		let decoded_b1: Log = DecodeHidden::decode(&mut &encoded_b1[..]).unwrap();
		assert_eq!(b1, decoded_b1);

		// encode/decode system item
		let auth_change: Log = a::RawLog::AuthoritiesChange::<u64>(vec![100, 200, 300]).into();
		let encoded_auth_change = auth_change.encode();
		let decoded_auth_change: Log = DecodeHidden::decode(&mut &encoded_auth_change[..]).unwrap();
		assert_eq!(auth_change, decoded_auth_change);

		// interpret regular item using `generic::DigestItem`
		let generic_b1: super::generic::DigestItem<H256, u64> = DecodeHidden::decode(&mut &encoded_b1[..]).unwrap();
		match generic_b1 {
			super::generic::DigestItem::Other(_) => (),
			_ => panic!("unexpected generic_b1: {:?}", generic_b1),
		}

		// interpret system item using `generic::DigestItem`
		let generic_auth_change: super::generic::DigestItem<H256, u64> = DecodeHidden::decode(&mut &encoded_auth_change[..]).unwrap();
		match generic_auth_change {
			super::generic::DigestItem::AuthoritiesChange::<H256, u64>(authorities) => assert_eq!(authorities, vec![100, 200, 300]),
			_ => panic!("unexpected generic_auth_change: {:?}", generic_auth_change),
		}

		// check that as-style methods are working with system items
		assert!(auth_change.as_authorities_change().is_some());

		// check that as-style methods are not working with regular items
		assert!(b1.as_authorities_change().is_none());
	}
}
