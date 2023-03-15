// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use codec::Encode;
use scale_info::{
	form::{Form, MetaForm, PortableForm},
	prelude::vec::Vec,
	IntoPortable, MetaType, Registry,
};

/// The intermediate representation for the runtime metadata.
/// Contains the needed context that allows conversion to multiple metadata versions.
///
/// # Note
///
/// Further fields could be added or removed to ensure proper conversion.
/// When the IR does not contain enough information to generate a specific version
/// of the runtime metadata an appropriate default value is used (ie, empty vector).
pub struct MetadataIR<T: Form = MetaForm> {
	/// Pallet metadata.
	pub pallets: Vec<PalletMetadataIR<T>>,
	/// Metadata of the extrinsic.
	pub extrinsic: ExtrinsicMetadataIR<T>,
	/// The type of the `Runtime`.
	pub ty: T::Type,
}

/// The intermediate representation for a pallet metadata.
#[derive(Clone, PartialEq, Eq, Encode, Debug)]
pub struct PalletMetadataIR<T: Form = MetaForm> {
	/// Pallet name.
	pub name: T::String,
	/// Pallet storage metadata.
	pub storage: Option<PalletStorageMetadataIR<T>>,
	/// Pallet calls metadata.
	pub calls: Option<PalletCallMetadataIR<T>>,
	/// Pallet event metadata.
	pub event: Option<PalletEventMetadataIR<T>>,
	/// Pallet constants metadata.
	pub constants: Vec<PalletConstantMetadataIR<T>>,
	/// Pallet error metadata.
	pub error: Option<PalletErrorMetadataIR<T>>,
	/// Define the index of the pallet, this index will be used for the encoding of pallet event,
	/// call and origin variants.
	pub index: u8,
	/// Pallet documentation.
	pub docs: Vec<T::String>,
}

impl IntoPortable for PalletMetadataIR {
	type Output = PalletMetadataIR<PortableForm>;

	fn into_portable(self, registry: &mut Registry) -> Self::Output {
		PalletMetadataIR {
			name: self.name.into_portable(registry),
			storage: self.storage.map(|storage| storage.into_portable(registry)),
			calls: self.calls.map(|calls| calls.into_portable(registry)),
			event: self.event.map(|event| event.into_portable(registry)),
			constants: registry.map_into_portable(self.constants),
			error: self.error.map(|error| error.into_portable(registry)),
			index: self.index,
			docs: registry.map_into_portable(self.docs),
		}
	}
}

/// Metadata of the extrinsic used by the runtime.
#[derive(Clone, PartialEq, Eq, Encode, Debug)]
pub struct ExtrinsicMetadataIR<T: Form = MetaForm> {
	/// The type of the extrinsic.
	pub ty: T::Type,
	/// Extrinsic version.
	pub version: u8,
	/// The signed extensions in the order they appear in the extrinsic.
	pub signed_extensions: Vec<SignedExtensionMetadataIR<T>>,
}

impl IntoPortable for ExtrinsicMetadataIR {
	type Output = ExtrinsicMetadataIR<PortableForm>;

	fn into_portable(self, registry: &mut Registry) -> Self::Output {
		ExtrinsicMetadataIR {
			ty: registry.register_type(&self.ty),
			version: self.version,
			signed_extensions: registry.map_into_portable(self.signed_extensions),
		}
	}
}

/// Metadata of an extrinsic's signed extension.
#[derive(Clone, PartialEq, Eq, Encode, Debug)]
pub struct SignedExtensionMetadataIR<T: Form = MetaForm> {
	/// The unique signed extension identifier, which may be different from the type name.
	pub identifier: T::String,
	/// The type of the signed extension, with the data to be included in the extrinsic.
	pub ty: T::Type,
	/// The type of the additional signed data, with the data to be included in the signed payload
	pub additional_signed: T::Type,
}

impl IntoPortable for SignedExtensionMetadataIR {
	type Output = SignedExtensionMetadataIR<PortableForm>;

	fn into_portable(self, registry: &mut Registry) -> Self::Output {
		SignedExtensionMetadataIR {
			identifier: self.identifier.into_portable(registry),
			ty: registry.register_type(&self.ty),
			additional_signed: registry.register_type(&self.additional_signed),
		}
	}
}

/// All metadata of the pallet's storage.
#[derive(Clone, PartialEq, Eq, Encode, Debug)]
/// The common prefix used by all storage entries.
pub struct PalletStorageMetadataIR<T: Form = MetaForm> {
	/// The common prefix used by all storage entries.
	pub prefix: T::String,
	/// Metadata for all storage entries.
	pub entries: Vec<StorageEntryMetadataIR<T>>,
}

impl IntoPortable for PalletStorageMetadataIR {
	type Output = PalletStorageMetadataIR<PortableForm>;

	fn into_portable(self, registry: &mut Registry) -> Self::Output {
		PalletStorageMetadataIR {
			prefix: self.prefix.into_portable(registry),
			entries: registry.map_into_portable(self.entries),
		}
	}
}

/// Metadata about one storage entry.
#[derive(Clone, PartialEq, Eq, Encode, Debug)]
pub struct StorageEntryMetadataIR<T: Form = MetaForm> {
	/// Variable name of the storage entry.
	pub name: T::String,
	/// An `Option` modifier of that storage entry.
	pub modifier: StorageEntryModifierIR,
	/// Type of the value stored in the entry.
	pub ty: StorageEntryTypeIR<T>,
	/// Default value (SCALE encoded).
	pub default: Vec<u8>,
	/// Storage entry documentation.
	pub docs: Vec<T::String>,
}

impl IntoPortable for StorageEntryMetadataIR {
	type Output = StorageEntryMetadataIR<PortableForm>;

	fn into_portable(self, registry: &mut Registry) -> Self::Output {
		StorageEntryMetadataIR {
			name: self.name.into_portable(registry),
			modifier: self.modifier,
			ty: self.ty.into_portable(registry),
			default: self.default,
			docs: registry.map_into_portable(self.docs),
		}
	}
}

/// A storage entry modifier indicates how a storage entry is returned when fetched and what the
/// value will be if the key is not present. Specifically this refers to the "return type" when
/// fetching a storage entry, and what the value will be if the key is not present.
///
/// `Optional` means you should expect an `Option<T>`, with `None` returned if the key is not
/// present. `Default` means you should expect a `T` with the default value of default if the key is
/// not present.
#[derive(Clone, PartialEq, Eq, Encode, Debug)]
pub enum StorageEntryModifierIR {
	/// The storage entry returns an `Option<T>`, with `None` if the key is not present.
	Optional,
	/// The storage entry returns `T::Default` if the key is not present.
	Default,
}

/// Hasher used by storage maps
#[derive(Clone, PartialEq, Eq, Encode, Debug)]
pub enum StorageHasherIR {
	/// 128-bit Blake2 hash.
	Blake2_128,
	/// 256-bit Blake2 hash.
	Blake2_256,
	/// Multiple 128-bit Blake2 hashes concatenated.
	Blake2_128Concat,
	/// 128-bit XX hash.
	Twox128,
	/// 256-bit XX hash.
	Twox256,
	/// Multiple 64-bit XX hashes concatenated.
	Twox64Concat,
	/// Identity hashing (no hashing).
	Identity,
}

/// A type of storage value.
#[derive(Clone, PartialEq, Eq, Encode, Debug)]
pub enum StorageEntryTypeIR<T: Form = MetaForm> {
	/// Plain storage entry (just the value).
	Plain(T::Type),
	/// A storage map.
	Map {
		/// One or more hashers, should be one hasher per key element.
		hashers: Vec<StorageHasherIR>,
		/// The type of the key, can be a tuple with elements for each of the hashers.
		key: T::Type,
		/// The type of the value.
		value: T::Type,
	},
}

impl IntoPortable for StorageEntryTypeIR {
	type Output = StorageEntryTypeIR<PortableForm>;

	fn into_portable(self, registry: &mut Registry) -> Self::Output {
		match self {
			Self::Plain(plain) => StorageEntryTypeIR::Plain(registry.register_type(&plain)),
			Self::Map { hashers, key, value } => StorageEntryTypeIR::Map {
				hashers,
				key: registry.register_type(&key),
				value: registry.register_type(&value),
			},
		}
	}
}

/// Metadata for all calls in a pallet
#[derive(Clone, PartialEq, Eq, Encode, Debug)]
pub struct PalletCallMetadataIR<T: Form = MetaForm> {
	/// The corresponding enum type for the pallet call.
	pub ty: T::Type,
}

impl IntoPortable for PalletCallMetadataIR {
	type Output = PalletCallMetadataIR<PortableForm>;

	fn into_portable(self, registry: &mut Registry) -> Self::Output {
		PalletCallMetadataIR { ty: registry.register_type(&self.ty) }
	}
}

impl From<MetaType> for PalletCallMetadataIR {
	fn from(ty: MetaType) -> Self {
		Self { ty }
	}
}

/// Metadata about the pallet Event type.
#[derive(Clone, PartialEq, Eq, Encode, Debug)]
pub struct PalletEventMetadataIR<T: Form = MetaForm> {
	/// The Event type.
	pub ty: T::Type,
}

impl IntoPortable for PalletEventMetadataIR {
	type Output = PalletEventMetadataIR<PortableForm>;

	fn into_portable(self, registry: &mut Registry) -> Self::Output {
		PalletEventMetadataIR { ty: registry.register_type(&self.ty) }
	}
}

impl From<MetaType> for PalletEventMetadataIR {
	fn from(ty: MetaType) -> Self {
		Self { ty }
	}
}

/// Metadata about one pallet constant.
#[derive(Clone, PartialEq, Eq, Encode, Debug)]
pub struct PalletConstantMetadataIR<T: Form = MetaForm> {
	/// Name of the pallet constant.
	pub name: T::String,
	/// Type of the pallet constant.
	pub ty: T::Type,
	/// Value stored in the constant (SCALE encoded).
	pub value: Vec<u8>,
	/// Documentation of the constant.
	pub docs: Vec<T::String>,
}

impl IntoPortable for PalletConstantMetadataIR {
	type Output = PalletConstantMetadataIR<PortableForm>;

	fn into_portable(self, registry: &mut Registry) -> Self::Output {
		PalletConstantMetadataIR {
			name: self.name.into_portable(registry),
			ty: registry.register_type(&self.ty),
			value: self.value,
			docs: registry.map_into_portable(self.docs),
		}
	}
}

/// Metadata about a pallet error.
#[derive(Clone, PartialEq, Eq, Encode, Debug)]
pub struct PalletErrorMetadataIR<T: Form = MetaForm> {
	/// The error type information.
	pub ty: T::Type,
}

impl IntoPortable for PalletErrorMetadataIR {
	type Output = PalletErrorMetadataIR<PortableForm>;

	fn into_portable(self, registry: &mut Registry) -> Self::Output {
		PalletErrorMetadataIR { ty: registry.register_type(&self.ty) }
	}
}

impl From<MetaType> for PalletErrorMetadataIR {
	fn from(ty: MetaType) -> Self {
		Self { ty }
	}
}
