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

//! Version module for runtime; Provide a function that returns runtime verion.

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
pub type MaybeCowString = ::std::borrow::Cow<'static, str>;
#[cfg(not(feature = "std"))]
pub type MaybeCowString = &'static str;

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

#[derive(Clone)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct RuntimeVersion {
	pub spec_name: MaybeCowString,
	pub impl_name: MaybeCowString,
	pub authoring_version: u32,
	pub spec_version: u32,
	pub impl_version: u32,
}

#[cfg(feature = "std")]
impl RuntimeVersion {
	/// Check if this version matches other version for calling into runtime.
	pub fn can_call_with(&self, other: &RuntimeVersion) -> bool {
		self.spec_version == other.spec_version &&
		self.spec_name == other.spec_name
	}

	/// Check if this version matches other version for authoring blocks.
	pub fn can_author_with(&self, other: &RuntimeVersion) -> bool {
		self.can_call_with(other) &&
		self.authoring_version == other.authoring_version
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
			spec_name: Cow::Owned(String::from_utf8(Slicable::decode(value)?).expect("Invalid utf-8 version string")),
			impl_name: Cow::Owned(String::from_utf8(Slicable::decode(value)?).expect("Invalid utf-8 version string")),
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
	/// Get runtime verions
	pub fn version() -> RuntimeVersion {
		T::VERSION.clone()
	}
}
