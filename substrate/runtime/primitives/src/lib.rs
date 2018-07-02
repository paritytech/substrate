// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! System manager: Handles all of the top-level stuff; executing block/transaction, setting code
//! and depositing logs.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
extern crate serde;

#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;

extern crate num_traits;
extern crate integer_sqrt;
extern crate substrate_runtime_std as rstd;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_runtime_support as runtime_support;
extern crate substrate_codec as codec;
extern crate substrate_primitives;

#[cfg(test)]
extern crate serde_json;

#[cfg(feature = "std")]
use std::collections::HashMap;

use rstd::prelude::*;
use substrate_primitives::hash::{H256, H512};

#[cfg(feature = "std")]
pub mod testing;

pub mod traits;
pub mod generic;
pub mod bft;

use traits::{Verify, Lazy};

/// A set of key value pairs for storage.
#[cfg(feature = "std")]
pub type StorageMap = HashMap<Vec<u8>, Vec<u8>>;

/// Complex storage builder stuff.
#[cfg(feature = "std")]
pub trait BuildStorage {
	fn build_storage(self) -> Result<StorageMap, String>;
}

#[cfg(feature = "std")]
impl BuildStorage for StorageMap {
	fn build_storage(self) -> Result<StorageMap, String> {
		Ok(self)
	}
}

/// Ed25519 signature verify.
#[derive(Eq, PartialEq, Clone, Default)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct Ed25519Signature(pub H512);

impl Verify for Ed25519Signature {
	type Signer = H256;
	fn verify<L: Lazy<[u8]>>(&self, mut msg: L, signer: &Self::Signer) -> bool {
		runtime_io::ed25519_verify(&(self.0).0, msg.get(), &signer.0[..])
	}
}

impl codec::Slicable for Ed25519Signature {
	fn decode<I: codec::Input>(input: &mut I) -> Option<Self> { Some(Ed25519Signature(codec::Slicable::decode(input)?,)) }
	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R { self.0.using_encoded(f) }
}

impl From<H512> for Ed25519Signature {
	fn from(h: H512) -> Ed25519Signature {
		Ed25519Signature(h)
	}
}

#[derive(Eq, PartialEq, Clone, Copy)]
#[cfg_attr(feature = "std", derive(Debug, Serialize))]
#[repr(u8)]
/// Outcome of a valid extrinsic application. Capable of being sliced.
pub enum ApplyOutcome {
	/// Successful application (extrinsic reported no issue).
	Success = 0,
	/// Failed application (extrinsic was probably a no-op other than fees).
	Fail = 1,
}
impl codec::Slicable for ApplyOutcome {
	fn decode<I: codec::Input>(input: &mut I) -> Option<Self> {
		match input.read_byte()? {
			x if x == ApplyOutcome::Success as u8 => Some(ApplyOutcome::Success),
			x if x == ApplyOutcome::Fail as u8 => Some(ApplyOutcome::Fail),
			_ => None,
		}
	}
	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(&[*self as u8])
	}
}

#[derive(Eq, PartialEq, Clone, Copy)]
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
impl codec::Slicable for ApplyError {
	fn decode<I: codec::Input>(input: &mut I) -> Option<Self> {
		match input.read_byte()? {
			x if x == ApplyError::BadSignature as u8 => Some(ApplyError::BadSignature),
			x if x == ApplyError::Stale as u8 => Some(ApplyError::Stale),
			x if x == ApplyError::Future as u8 => Some(ApplyError::Future),
			x if x == ApplyError::CantPay as u8 => Some(ApplyError::CantPay),
			_ => None,
		}
	}
	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(&[*self as u8])
	}
}

/// Result from attempt to apply an extrinsic.
pub type ApplyResult = Result<ApplyOutcome, ApplyError>;

/// Potentially "unsigned" signature verification.
#[derive(Eq, PartialEq, Clone, Default)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct MaybeUnsigned<T>(pub T);

impl<T: Verify> MaybeUnsigned<T> where
	T: Default + Eq,
	<T as Verify>::Signer: Default + Eq,
{
	fn is_signed(&self) -> bool {
		self.0 != T::default()
	}

	fn is_addressed(&self, signer: &<Self as Verify>::Signer) -> bool {
		signer != &Default::default()
	}
}

impl<T: Verify> Verify for MaybeUnsigned<T> where
	T: Default + Eq,
	<T as Verify>::Signer: Default + Eq,
{
	type Signer = T::Signer;
	fn verify<L: Lazy<[u8]>>(&self, msg: L, signer: &Self::Signer) -> bool {
		if !self.is_signed() {
			!self.is_addressed(signer)
		} else {
			self.0.verify(msg, signer)
		}
	}
}

impl<T: codec::Slicable> codec::Slicable for MaybeUnsigned<T> {
	fn decode<I: codec::Input>(input: &mut I) -> Option<Self> { Some(MaybeUnsigned(codec::Slicable::decode(input)?)) }
	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R { self.0.using_encoded(f) }
}

impl<T> From<T> for MaybeUnsigned<T> {
	fn from(t: T) -> Self {
		MaybeUnsigned(t)
	}
}

/// Verify a signature on an encoded value in a lazy manner. This can be
/// an optimization if the signature scheme has an "unsigned" escape hash.
pub fn verify_encoded_lazy<V: Verify, T: codec::Slicable>(sig: &V, item: &T, signer: &V::Signer) -> bool {
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
	($concrete:ident $config:ident $snake:ident $($rest:ident)*) => {
		#[cfg(any(feature = "std", test))]
		pub type $config = $snake::GenesisConfig<$concrete>;
		__impl_outer_config_types! {$concrete $($rest)*}
	};
	($concrete:ident) => ()
}

#[macro_export]
/// Implement the output "meta" module configuration struct.
macro_rules! impl_outer_config {
	( pub struct $main:ident for $concrete:ident { $( $config:ident => $snake:ident, )* } ) => {
		__impl_outer_config_types! { $concrete $( $config $snake )* }
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
			fn build_storage(self) -> ::std::result::Result<$crate::StorageMap, String> {
				let mut s = $crate::StorageMap::new();
				$(
					if let Some(extra) = self.$snake {
						s.extend(extra.build_storage()?);
					}
				)*
				Ok(s)
			}
		}
	}
}
