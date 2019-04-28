// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Decodable variant of the RuntimeMetadata.
//!
//! This really doesn't belong here, but is necessary for the moment. In the future
//! it should be removed entirely to an external module for shimming on to the
//! codec-encoded metadata.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
use serde::Serialize;
#[cfg(feature = "std")]
use parity_codec::{Decode, Input};
use parity_codec::{Encode, Output};
use rstd::vec::Vec;

#[cfg(feature = "std")]
type StringBuf = String;

/// Curent prefix of metadata
pub const META_RESERVED: u32 = 0x6174656d; // 'meta' warn endianness

/// On `no_std` we do not support `Decode` and thus `StringBuf` is just `&'static str`.
/// So, if someone tries to decode this stuff on `no_std`, they will get a compilation error.
#[cfg(not(feature = "std"))]
type StringBuf = &'static str;

/// A type that decodes to a different type than it encodes.
/// The user needs to make sure that both types use the same encoding.
///
/// For example a `&'static [ &'static str ]` can be decoded to a `Vec<String>`.
#[derive(Clone)]
pub enum DecodeDifferent<B, O> where B: 'static, O: 'static {
	Encode(B),
	Decoded(O),
}

impl<B, O> Encode for DecodeDifferent<B, O> where B: Encode + 'static, O: Encode + 'static {
	fn encode_to<W: Output>(&self, dest: &mut W) {
		match self {
			DecodeDifferent::Encode(b) => b.encode_to(dest),
			DecodeDifferent::Decoded(o) => o.encode_to(dest),
		}
	}
}

#[cfg(feature = "std")]
impl<B, O> Decode for DecodeDifferent<B, O> where B: 'static, O: Decode + 'static {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		<O>::decode(input).and_then(|val| {
			Some(DecodeDifferent::Decoded(val))
		})
	}
}

impl<B, O> PartialEq for DecodeDifferent<B, O>
where
	B: Encode + Eq + PartialEq + 'static,
	O: Encode + Eq + PartialEq + 'static,
{
	fn eq(&self, other: &Self) -> bool {
		self.encode() == other.encode()
	}
}

impl<B, O> Eq for DecodeDifferent<B, O>
	where B: Encode + Eq + PartialEq + 'static, O: Encode + Eq + PartialEq + 'static
{}

#[cfg(feature = "std")]
impl<B, O> std::fmt::Debug for DecodeDifferent<B, O>
	where
		B: std::fmt::Debug + Eq + 'static,
		O: std::fmt::Debug + Eq + 'static,
{
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		match self {
			DecodeDifferent::Encode(b) => b.fmt(f),
			DecodeDifferent::Decoded(o) => o.fmt(f),
		}
	}
}

#[cfg(feature = "std")]
impl<B, O> serde::Serialize for DecodeDifferent<B, O>
	where
		B: serde::Serialize + 'static,
		O: serde::Serialize + 'static,
{
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
		where
				S: serde::Serializer,
	{
		match self {
			DecodeDifferent::Encode(b) => b.serialize(serializer),
			DecodeDifferent::Decoded(o) => o.serialize(serializer),
		}
	}
}

pub type DecodeDifferentArray<B, O=B> = DecodeDifferent<&'static [B], Vec<O>>;

#[cfg(feature = "std")]
type DecodeDifferentStr = DecodeDifferent<&'static str, StringBuf>;
#[cfg(not(feature = "std"))]
type DecodeDifferentStr = DecodeDifferent<&'static str, StringBuf>;

/// All the metadata about a function.
#[derive(Clone, PartialEq, Eq, Encode)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub struct FunctionMetadata {
	pub name: DecodeDifferentStr,
	pub arguments: DecodeDifferentArray<FunctionArgumentMetadata>,
	pub documentation: DecodeDifferentArray<&'static str, StringBuf>,
}

/// All the metadata about a function argument.
#[derive(Clone, PartialEq, Eq, Encode)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub struct FunctionArgumentMetadata {
	pub name: DecodeDifferentStr,
	pub ty: DecodeDifferentStr,
}

/// Newtype wrapper for support encoding functions (actual the result of the function).
#[derive(Clone, Eq)]
pub struct FnEncode<E>(pub fn() -> E) where E: Encode + 'static;

impl<E: Encode> Encode for FnEncode<E> {
	fn encode_to<W: Output>(&self, dest: &mut W) {
		self.0().encode_to(dest);
	}
}

impl<E: Encode + PartialEq> PartialEq for FnEncode<E> {
	fn eq(&self, other: &Self) -> bool {
		self.0().eq(&other.0())
	}
}

#[cfg(feature = "std")]
impl<E: Encode + ::std::fmt::Debug> std::fmt::Debug for FnEncode<E> {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		self.0().fmt(f)
	}
}

#[cfg(feature = "std")]
impl<E: Encode + serde::Serialize> serde::Serialize for FnEncode<E> {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
		where
				S: serde::Serializer,
	{
		self.0().serialize(serializer)
	}
}

/// All the metadata about an outer event.
#[derive(Clone, PartialEq, Eq, Encode)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub struct OuterEventMetadata {
	pub name: DecodeDifferentStr,
	pub events: DecodeDifferentArray<
		(&'static str, FnEncode<&'static [EventMetadata]>),
		(StringBuf, Vec<EventMetadata>)
	>,
}

/// All the metadata about a event.
#[derive(Clone, PartialEq, Eq, Encode)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub struct EventMetadata {
	pub name: DecodeDifferentStr,
	pub arguments: DecodeDifferentArray<&'static str, StringBuf>,
	pub documentation: DecodeDifferentArray<&'static str, StringBuf>,
}

/// All the metadata about a storage.
#[derive(Clone, PartialEq, Eq, Encode)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub struct StorageMetadata {
	pub functions: DecodeDifferentArray<StorageFunctionMetadata>,
}

/// All the metadata about a storage function.
#[derive(Clone, PartialEq, Eq, Encode)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub struct StorageFunctionMetadata {
	pub name: DecodeDifferentStr,
	pub modifier: StorageFunctionModifier,
	pub ty: StorageFunctionType,
	pub default: ByteGetter,
	pub documentation: DecodeDifferentArray<&'static str, StringBuf>,
}

/// A technical trait to store lazy initiated vec value as static dyn pointer.
pub trait DefaultByte {
	fn default_byte(&self) -> Vec<u8>;
}

/// Wrapper over dyn pointer for accessing a cached once byte value.
#[derive(Clone)]
pub struct DefaultByteGetter(pub &'static dyn DefaultByte);

/// Decode different for static lazy initiated byte value.
pub type ByteGetter = DecodeDifferent<DefaultByteGetter, Vec<u8>>;

impl Encode for DefaultByteGetter {
	fn encode_to<W: Output>(&self, dest: &mut W) {
		self.0.default_byte().encode_to(dest)
	}
}

impl PartialEq<DefaultByteGetter> for DefaultByteGetter {
	fn eq(&self, other: &DefaultByteGetter) -> bool {
		let left = self.0.default_byte();
		let right = other.0.default_byte();
		left.eq(&right)
	}
}

impl Eq for DefaultByteGetter { }

#[cfg(feature = "std")]
impl serde::Serialize for DefaultByteGetter {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
		where
				S: serde::Serializer,
	{
		self.0.default_byte().serialize(serializer)
	}
}

#[cfg(feature = "std")]
impl std::fmt::Debug for DefaultByteGetter {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		self.0.default_byte().fmt(f)
	}
}

/// Hasher used by storage maps
#[derive(Clone, PartialEq, Eq, Encode)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub enum StorageHasher {
	Blake2_128,
	Blake2_256,
	Twox128,
	Twox256,
	Twox64Concat,
}

/// A storage function type.
#[derive(Clone, PartialEq, Eq, Encode)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub enum StorageFunctionType {
	Plain(DecodeDifferentStr),
	Map {
		hasher: StorageHasher,
		key: DecodeDifferentStr,
		value: DecodeDifferentStr,
		is_linked: bool,
	},
	DoubleMap {
		hasher: StorageHasher,
		key1: DecodeDifferentStr,
		key2: DecodeDifferentStr,
		value: DecodeDifferentStr,
		key2_hasher: DecodeDifferentStr,
	},
}

/// A storage function modifier.
#[derive(Clone, PartialEq, Eq, Encode)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub enum StorageFunctionModifier {
	Optional,
	Default,
}

/// All metadata about the outer dispatch.
#[derive(Clone, PartialEq, Eq, Encode)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub struct OuterDispatchMetadata {
	pub name: DecodeDifferentStr,
	pub calls: DecodeDifferentArray<OuterDispatchCall>,
}

/// A Call from the outer dispatch.
#[derive(Clone, PartialEq, Eq, Encode)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub struct OuterDispatchCall {
	pub name: DecodeDifferentStr,
	pub index: u16,
}

#[derive(Eq, Encode, PartialEq)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
/// Metadata prefixed by a u32 for reserved usage
pub struct RuntimeMetadataPrefixed(pub u32, pub RuntimeMetadata);

/// The metadata of a runtime.
/// The version ID encoded/decoded through
/// the enum nature of `RuntimeMetadata`.
#[derive(Eq, Encode, PartialEq)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub enum RuntimeMetadata {
	/// Unused; enum filler.
	V0(RuntimeMetadataDeprecated),
	/// Version 1 for runtime metadata. No longer used.
	V1(RuntimeMetadataDeprecated),
	/// Version 2 for runtime metadata. No longer used.
	V2(RuntimeMetadataDeprecated),
	/// Version 3 for runtime metadata. No longer used.
	V3(RuntimeMetadataDeprecated),
	/// Version 4 for runtime metadata.
	V4(RuntimeMetadataV4),
}

/// Enum that should fail.
#[derive(Eq, PartialEq)]
#[cfg_attr(feature = "std", derive(Debug, Serialize))]
pub enum RuntimeMetadataDeprecated { }

impl Encode for RuntimeMetadataDeprecated {
	fn encode_to<W: Output>(&self, _dest: &mut W) {
	}
}

#[cfg(feature = "std")]
impl Decode for RuntimeMetadataDeprecated {
	fn decode<I: Input>(_input: &mut I) -> Option<Self> {
		unimplemented!()
	}
}

/// The metadata of a runtime.
#[derive(Eq, Encode, PartialEq)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub struct RuntimeMetadataV4 {
	pub modules: DecodeDifferentArray<ModuleMetadata>,
}

/// All metadata about an runtime module.
#[derive(Clone, PartialEq, Eq, Encode)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub struct ModuleMetadata {
	pub name: DecodeDifferentStr,
	pub prefix: DecodeDifferent<FnEncode<&'static str>, StringBuf>,
	pub storage: ODFnA<StorageFunctionMetadata>,
	pub calls: ODFnA<FunctionMetadata>,
	pub event: ODFnA<EventMetadata>,
}

type ODFnA<T> = Option<DecodeDifferent<FnEncode<&'static [T]>, Vec<T>>>;

impl Into<primitives::OpaqueMetadata> for RuntimeMetadataPrefixed {
	fn into(self) -> primitives::OpaqueMetadata {
		primitives::OpaqueMetadata::new(self.encode())
	}
}

impl Into<RuntimeMetadataPrefixed> for RuntimeMetadata {
	fn into(self) -> RuntimeMetadataPrefixed {
		RuntimeMetadataPrefixed(META_RESERVED, self)
	}
}
