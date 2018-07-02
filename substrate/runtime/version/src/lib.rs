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

//! Version module for runtime; Provide a function that returns runtime version.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
extern crate serde;

#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;

#[allow(unused_imports)]
#[macro_use]
extern crate substrate_runtime_std as rstd;

#[macro_use]
extern crate substrate_runtime_support as runtime_support;

extern crate substrate_codec as codec;

use rstd::prelude::*;
use codec::Slicable;
#[cfg(feature = "std")]
use std::borrow::Cow;

#[cfg(feature = "std")]
pub type VersionString = ::std::borrow::Cow<'static, str>;
#[cfg(not(feature = "std"))]
pub type VersionString = &'static str;

#[cfg(feature = "std")]
#[macro_export]
macro_rules! ver_str {
	( $y:expr ) => {{ ::std::borrow::Cow::Borrowed($y) }}
}

#[cfg(not(feature = "std"))]
#[macro_export]
macro_rules! ver_str {
	( $y:expr ) => {{ $y }}
}

/// Runtime version.
/// This should not be thought of as classic Semver (major/minor/tiny).
/// This triplet have different semantics and mis-interpretation could cause problems.
/// In particular: bug fixes should result in an increment of `spec_version` and possibly `authoring_version`,
/// absolutely not `impl_version` since they change the semantics of the runtime.
#[derive(Clone)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct RuntimeVersion {
	/// Identifies the different Substrate runtimes. There'll be at least polkadot and demo. A different on-chain spec_name to that of the native runtime would normally result in node not attempting to sync further.
	pub spec_name: VersionString,
	/// Name of the implementation of the spec. This is of little consequence for the node and serves only to differentiate code of different implementation teams. For this codebase, it will be parity-polkadot.
	/// If there were a non-Rust implementation of the Polkadot runtime (e.g. C++), then it would identify itself with an accordingly different impl_name.
	pub impl_name: VersionString,
	/// `authoring_version` is the version of the authorship interface. An authoring node will not attempt to author blocks unless this is equal to its native runtime.
	pub authoring_version: u32,
	/// Version of the runtime specification. A full-node will not attempt to use its native runtime in substitute for the on-chain Wasm runtime unless all of `spec_name`, `spec_version` and `authoring_version`
	/// are the same between Wasm and native.
	pub spec_version: u32,
	/// Version of the implementation of the specification. Nodes are free to ignore this; it serves only as an indication that the code is different;
	/// as long as the other two versions are the same then while the code may be different, it is nonetheless required to do the same thing.
	/// Non-consensus-breaking optimisations are about the only changes that could be made which would result in only the impl_version changing.
	pub impl_version: u32,
}

// TODO: remove this after PoC-2
#[cfg(feature = "std")]
impl Default for RuntimeVersion {
	fn default() -> RuntimeVersion {
		RuntimeVersion {
			spec_name: ver_str!("polkadot"),
			impl_name: ver_str!("parity-polkadot"),
			authoring_version: 0,
			spec_version: 0,
			impl_version: 0,
		}
	}
}

#[cfg(feature = "std")]
impl RuntimeVersion {
	/// Check if this version matches other version for calling into runtime.
	pub fn can_call_with(&self, other: &RuntimeVersion) -> bool {
		self.spec_version == other.spec_version &&
		self.spec_name == other.spec_name &&
		self.authoring_version == other.authoring_version
	}

	/// Check if this version matches other version for authoring blocks.
	pub fn can_author_with(&self, other: &RuntimeVersion) -> bool {
		self.authoring_version == other.authoring_version &&
		self.spec_name == other.spec_name
	}
}

impl Slicable for RuntimeVersion {
	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();
		v.extend(codec::encode_slice(self.spec_name.as_bytes()));
		v.extend(codec::encode_slice(self.impl_name.as_bytes()));
		self.authoring_version.using_encoded(|s| v.extend(s));
		self.spec_version.using_encoded(|s| v.extend(s));
		self.impl_version.using_encoded(|s| v.extend(s));
		v
	}

	#[cfg(not(feature = "std"))]
	fn decode<I: codec::Input>(_value: &mut I) -> Option<Self> {
		unreachable!()
	}

	#[cfg(feature = "std")]
	fn decode<I: codec::Input>(value: &mut I) -> Option<Self> {
		Some(RuntimeVersion {
			spec_name: Cow::Owned(String::from_utf8_lossy(&Vec::decode(value)?).into()),
			impl_name: Cow::Owned(String::from_utf8_lossy(&Vec::decode(value)?).into()),
			authoring_version: Slicable::decode(value)?,
			spec_version: Slicable::decode(value)?,
			impl_version: Slicable::decode(value)?,
		})
	}
}

pub trait Trait {
	const VERSION: RuntimeVersion;
}

decl_module! {
	pub struct Module<T: Trait>;
}

impl<T: Trait> Module<T> {
	/// Get runtime version.
	pub fn version() -> RuntimeVersion {
		T::VERSION.clone()
	}
}
