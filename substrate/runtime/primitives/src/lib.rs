// Copyright 2017 Parity Technologies (UK) Ltd.
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
extern crate substrate_codec_derive;

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
use substrate_primitives::hexdisplay::ascii_format;

#[cfg(feature = "std")]
pub mod testing;

pub mod traits;
pub mod generic;
pub mod bft;

use traits::{Verify, Lazy};

#[cfg(feature = "std")]
pub use serde::{Serialize, de::DeserializeOwned};

/// A set of key value pairs for storage.
#[cfg(feature = "std")]
pub type StorageMap = HashMap<Vec<u8>, Vec<u8>>;

/// Complex storage builder stuff.
#[cfg(feature = "std")]
pub trait BuildStorage {
	fn hash(data: &[u8]) -> [u8; 16] {
		let r = runtime_io::twox_128(data);
		trace!(target: "build_storage", "{} <= {}", substrate_primitives::hexdisplay::HexDisplay::from(&r), ascii_format(data));
		r
	}
	fn build_storage(self) -> Result<StorageMap, String>;
}

#[cfg(feature = "std")]
impl BuildStorage for StorageMap {
	fn build_storage(self) -> Result<StorageMap, String> {
		Ok(self)
	}
}

/// Permill is parts-per-million (i.e. after multiplying by this, divide by 1000000).
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[derive(Encode, Decode, Default, Copy, Clone, PartialEq, Eq)]
pub struct Permill(u32);

// TODO: impl Mul<Permill> for N where N: As<usize>
impl Permill {
	pub fn times<N: traits::As<usize> + ::rstd::ops::Mul<N, Output=N> + ::rstd::ops::Div<N, Output=N>>(self, b: N) -> N {
		// TODO: handle overflows
		b * <N as traits::As<usize>>::sa(self.0 as usize) / <N as traits::As<usize>>::sa(1000000)
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

/// Ed25519 signature verify.
#[derive(Eq, PartialEq, Clone, Default, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct Ed25519Signature(pub H512);

impl Verify for Ed25519Signature {
	type Signer = H256;
	fn verify<L: Lazy<[u8]>>(&self, mut msg: L, signer: &Self::Signer) -> bool {
		runtime_io::ed25519_verify(&(self.0).0, msg.get(), &signer.0[..])
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
