// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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
use serde::{Serialize, Deserialize};
#[cfg(feature = "std")]
use std::fmt;
#[cfg(feature = "std")]
use std::collections::HashSet;

use codec::{Encode, Decode};
use sp_runtime::RuntimeString;
pub use sp_runtime::create_runtime_str;
#[doc(hidden)]
pub use sp_std;

#[cfg(feature = "std")]
use sp_runtime::{traits::Block as BlockT, generic::BlockId};

/// The identity of a particular API interface that the runtime might provide.
pub type ApiId = [u8; 8];

/// A vector of pairs of `ApiId` and a `u32` for version.
pub type ApisVec = sp_std::borrow::Cow<'static, [(ApiId, u32)]>;

/// Create a vector of Api declarations.
#[macro_export]
macro_rules! create_apis_vec {
	( $y:expr ) => { $crate::sp_std::borrow::Cow::Borrowed(& $y) }
}

/// Runtime version.
/// This should not be thought of as classic Semver (major/minor/tiny).
/// This triplet have different semantics and mis-interpretation could cause problems.
/// In particular: bug fixes should result in an increment of `spec_version` and possibly `authoring_version`,
/// absolutely not `impl_version` since they change the semantics of the runtime.
#[derive(Clone, PartialEq, Eq, Encode, Decode, Default, sp_runtime::RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
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
	#[cfg_attr(
		feature = "std",
		serde(
			serialize_with = "apis_serialize::serialize",
			deserialize_with = "apis_serialize::deserialize",
		)
	)]
	pub apis: ApisVec,

	/// All existing dispatches are fully compatible when this number doesn't change. If this
	/// number changes, then `spec_version` must change, also.
	///
	/// This number must change when an existing dispatchable (module ID, dispatch ID) is changed,
	/// either through an alteration in its user-level semantics, a parameter added/removed/changed,
	/// a dispatchable being removed, a module being removed, or a dispatchable/module changing its
	/// index.
	///
	/// It need *not* change when a new module is added or when a dispatchable is added.
	pub transaction_version: u32,
}

#[cfg(feature = "std")]
impl fmt::Display for RuntimeVersion {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{}-{} ({}-{}.tx{}.au{})",
			self.spec_name,
			self.spec_version,
			self.impl_name,
			self.impl_version,
			self.transaction_version,
			self.authoring_version,
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

	/// Check if the given api with `api_id` is implemented and the version passes the given
	/// `predicate`.
	pub fn has_api_with<P: Fn(u32) -> bool>(
		&self,
		id: &ApiId,
		predicate: P,
	) -> bool {
		self.apis.iter().any(|(s, v)| s == id && predicate(*v))
	}
}

#[cfg(feature = "std")]
#[derive(Debug)]
pub struct NativeVersion {
	/// Basic runtime version info.
	pub runtime_version: RuntimeVersion,
	/// Authoring runtimes that this native runtime supports.
	pub can_author_with: HashSet<u32>,
}

#[cfg(feature = "std")]
impl NativeVersion {
	/// Check if this version matches other version for authoring blocks.
	///
	/// # Return
	///
	/// - Returns `Ok(())` when authoring is supported.
	/// - Returns `Err(_)` with a detailed error when authoring is not supported.
	pub fn can_author_with(&self, other: &RuntimeVersion) -> Result<(), String> {
		if self.runtime_version.spec_name != other.spec_name {
			Err(format!(
				"`spec_name` does not match `{}` vs `{}`",
				self.runtime_version.spec_name,
				other.spec_name,
			))
		} else if self.runtime_version.authoring_version != other.authoring_version
			&& !self.can_author_with.contains(&other.authoring_version)
		{
			Err(format!(
				"`authoring_version` does not match `{version}` vs `{other_version}` and \
				`can_author_with` not contains `{other_version}`",
				version = self.runtime_version.authoring_version,
				other_version = other.authoring_version,
			))
		} else {
			Ok(())
		}
	}
}

/// Something that can provide the runtime version at a given block and the native runtime version.
#[cfg(feature = "std")]
pub trait GetRuntimeVersion<Block: BlockT> {
	/// Returns the version of the native runtime.
	fn native_version(&self) -> &NativeVersion;

	/// Returns the version of runtime at the given block.
	fn runtime_version(&self, at: &BlockId<Block>) -> Result<RuntimeVersion, String>;
}

#[cfg(feature = "std")]
impl<T: GetRuntimeVersion<Block>, Block: BlockT> GetRuntimeVersion<Block> for std::sync::Arc<T> {
	fn native_version(&self) -> &NativeVersion {
		(&**self).native_version()
	}

	fn runtime_version(&self, at: &BlockId<Block>) -> Result<RuntimeVersion, String> {
		(&**self).runtime_version(at)
	}
}

#[cfg(feature = "std")]
mod apis_serialize {
	use super::*;
	use impl_serde::serialize as bytes;
	use serde::{Serializer, de, ser::SerializeTuple};

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

	pub fn serialize_bytesref<S>(&apis: &&super::ApiId, ser: S) -> Result<S::Ok, S::Error> where
		S: Serializer,
	{
		bytes::serialize(apis, ser)
	}

	#[derive(Deserialize)]
	struct ApiIdOwned(
		#[serde(deserialize_with="deserialize_bytes")]
		super::ApiId,
		u32,
	);

	pub fn deserialize<'de, D>(deserializer: D) -> Result<ApisVec, D::Error> where
		D: de::Deserializer<'de>,
	{
		struct Visitor;
		impl<'de> de::Visitor<'de> for Visitor {
			type Value = ApisVec;

			fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
				formatter.write_str("a sequence of api id and version tuples")
			}

			fn visit_seq<V>(self, mut visitor: V) -> Result<Self::Value, V::Error> where
				V: de::SeqAccess<'de>,
			{
				let mut apis = Vec::new();
				while let Some(value) = visitor.next_element::<ApiIdOwned>()? {
					apis.push((value.0, value.1));
				}
				Ok(apis.into())
			}
		}
		deserializer.deserialize_seq(Visitor)
	}

	pub fn deserialize_bytes<'de, D>(d: D) -> Result<super::ApiId, D::Error> where
		D: de::Deserializer<'de>
	{
		let mut arr = [0; 8];
		bytes::deserialize_check_len(d, bytes::ExpectedLen::Exact(&mut arr[..]))?;
		Ok(arr)
	}
}
