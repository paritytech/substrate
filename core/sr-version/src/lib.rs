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

//! Version module for the Substrate runtime; Provides a function that returns the runtime version.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
use serde::Serialize;
#[cfg(feature = "std")]
use std::fmt;
#[cfg(feature = "std")]
use std::collections::HashSet;
#[cfg(feature = "std")]
use runtime_primitives::traits::RuntimeApiInfo;

use parity_codec::Encode;
#[cfg(feature = "std")]
use parity_codec::Decode;
use runtime_primitives::RuntimeString;
pub use runtime_primitives::create_runtime_str;

/// The identity of a particular API interface that the runtime might provide.
pub type ApiId = [u8; 8];

/// A vector of pairs of `ApiId` and a `u32` for version. For `"std"` builds, this
/// is a `Cow`.
#[cfg(feature = "std")]
pub type ApisVec = ::std::borrow::Cow<'static, [(ApiId, u32)]>;
/// A vector of pairs of `ApiId` and a `u32` for version. For `"no-std"` builds, this
/// is just a reference.
#[cfg(not(feature = "std"))]
pub type ApisVec = &'static [(ApiId, u32)];

/// Create a vector of Api declarations.
#[macro_export]
#[cfg(feature = "std")]
macro_rules! create_apis_vec {
	( $y:expr ) => { ::std::borrow::Cow::Borrowed(& $y) }
}
#[macro_export]
#[cfg(not(feature = "std"))]
macro_rules! create_apis_vec {
	( $y:expr ) => { & $y }
}

/// Runtime version.
/// This should not be thought of as classic Semver (major/minor/tiny).
/// This triplet have different semantics and mis-interpretation could cause problems.
/// In particular: bug fixes should result in an increment of `spec_version` and possibly `authoring_version`,
/// absolutely not `impl_version` since they change the semantics of the runtime.
#[derive(Clone, PartialEq, Eq, Encode)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Decode))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
pub struct RuntimeVersion {
	/// Identifies the different Substrate runtimes. There'll be at least polkadot and node.
	/// A different on-chain spec_name to that of the native runtime would normally result
	/// in node not attempting to sync or author blocks.
	pub spec_name: RuntimeString,

	/// Name of the implementation of the spec. This is of little consequence for the node
	/// and serves only to differentiate code of different implementation teams. For this
	/// codebase, it will be parity-polkadot. If there were a non-Rust implementation of the
	/// Polkadot runtime (e.g. C++), then it would identify itself with an accordingly different
	/// `impl_name`.
	pub impl_name: RuntimeString,

	/// `authoring_version` is the version of the authorship interface. An authoring node
	/// will not attempt to author blocks unless this is equal to its native runtime.
	pub authoring_version: u32,

	/// Version of the runtime specification. A full-node will not attempt to use its native
	/// runtime in substitute for the on-chain Wasm runtime unless all of `spec_name`,
	/// `spec_version` and `authoring_version` are the same between Wasm and native.
	pub spec_version: u32,

	/// Version of the implementation of the specification. Nodes are free to ignore this; it
	/// serves only as an indication that the code is different; as long as the other two versions
	/// are the same then while the actual code may be different, it is nonetheless required to
	/// do the same thing.
	/// Non-consensus-breaking optimizations are about the only changes that could be made which
	/// would result in only the `impl_version` changing.
	pub impl_version: u32,

	/// List of supported API "features" along with their versions.
	#[cfg_attr(feature = "std", serde(serialize_with = "apis_serialize::serialize"))]
	pub apis: ApisVec,
}

#[cfg(feature = "std")]
impl fmt::Display for RuntimeVersion {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{}-{}:{}({}-{})",
			self.spec_name,
			self.spec_version,
			self.authoring_version,
			self.impl_name,
			self.impl_version
		)
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

	/// Check if this version supports a particular API.
	pub fn has_api<A: RuntimeApiInfo + ?Sized>(&self) -> bool {
		self.apis.iter().any(|(s, v)| {
			s == &A::ID && *v == A::VERSION
		})
	}

	/// Check if the given api is implemented and the version passes a predicate.
	pub fn has_api_with<A: RuntimeApiInfo + ?Sized, P: Fn(u32) -> bool>(
		&self,
		pred: P,
	) -> bool {
		self.apis.iter().any(|(s, v)| {
			s == &A::ID && pred(*v)
		})
	}
}

#[cfg(feature = "std")]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct NativeVersion {
	/// Basic runtime version info.
	pub runtime_version: RuntimeVersion,
	/// Authoring runtimes that this native runtime supports.
	pub can_author_with: HashSet<u32>,
}

#[cfg(feature = "std")]
impl NativeVersion {
	/// Check if this version matches other version for authoring blocks.
	pub fn can_author_with(&self, other: &RuntimeVersion) -> bool {
		self.runtime_version.spec_name == other.spec_name &&
			(self.runtime_version.authoring_version == other.authoring_version ||
			self.can_author_with.contains(&other.authoring_version))
	}
}

#[cfg(feature = "std")]
mod apis_serialize {
	use super::*;
	use impl_serde::serialize as bytes;
	use serde::{Serializer, ser::SerializeTuple};

	#[derive(Serialize)]
	struct ApiId<'a>(
		#[serde(serialize_with="serialize_bytesref")] &'a super::ApiId,
		&'a u32,
	);

	pub fn serialize<S>(apis: &ApisVec, ser: S) -> Result<S::Ok, S::Error> where
		S: Serializer,
	{
		let len = apis.len();
		let mut seq = ser.serialize_tuple(len)?;
		for (api, ver) in &**apis {
			seq.serialize_element(&ApiId(api, ver))?;
		}
		seq.end()
	}

	pub fn serialize_bytesref<S>(apis: &&super::ApiId, ser: S) -> Result<S::Ok, S::Error> where
		S: Serializer,
	{
		bytes::serialize(*apis, ser)
	}
}
