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

#[cfg(feature = "std")]
pub type BuiltExternalities = HashMap<Vec<u8>, Vec<u8>>;

#[cfg(feature = "std")]
pub trait BuildExternalities {
	fn build_externalities(self) -> BuiltExternalities;
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

/// Potentially "unsigned" signature verification.
#[derive(Eq, PartialEq, Clone, Default)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct MaybeUnsigned<T>(pub T);

impl<T: Verify> MaybeUnsigned<T> where
	T: Default + Eq,
	<T as Verify>::Signer: Default + Eq,
{
	fn is_signed(&self, signer: &<Self as Verify>::Signer) -> bool {
		self.0 != T::default() || signer != &<Self as Verify>::Signer::default()
	}
}

impl<T: Verify> Verify for MaybeUnsigned<T> where
	T: Default + Eq,
	<T as Verify>::Signer: Default + Eq,
{
	type Signer = T::Signer;
	fn verify<L: Lazy<[u8]>>(&self, msg: L, signer: &Self::Signer) -> bool {
		if !self.is_signed(signer) {
			true
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
		pub struct $main {
			$(
				pub $snake: Option<$config>,
			)*
		}
		#[cfg(any(feature = "std", test))]
		impl $crate::BuildExternalities for $main {
			fn build_externalities(self) -> $crate::BuiltExternalities {
				let mut s = $crate::BuiltExternalities::new();
				$(
					if let Some(extra) = self.$snake {
						s.extend(extra.build_externalities());
					}
				)*
				s
			}
		}
	}
}
