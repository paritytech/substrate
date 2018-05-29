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

#[cfg(feature = "std")]
use std::collections::HashMap;

use substrate_primitives::hash::H512;

#[cfg(feature = "std")]
pub mod testing;

pub mod traits;
pub mod generic;

#[cfg(feature = "std")]
pub type BuiltExternalities = HashMap<Vec<u8>, Vec<u8>>;

#[cfg(feature = "std")]
pub trait BuildExternalities {
	fn build_externalities(self) -> BuiltExternalities;
}

/// Ed25519 signature verify.
#[derive(Eq, PartialEq, Clone, Default)]
#[cfg_attr(feature = "std", derive(Debug, Serialize))]
pub struct Ed25519Signature(H512);
impl traits::Verify for Ed25519Signature {
	type Signer = [u8; 32];
	fn verify(&self, msg: &[u8], signer: &Self::Signer) -> bool {
		runtime_io::ed25519_verify(&(self.0).0, msg, &signer[..])
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
