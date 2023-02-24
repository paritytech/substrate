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
	/// Palet metadata.
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

use frame_metadata::v14::{
	ExtrinsicMetadata, PalletCallMetadata, PalletConstantMetadata, PalletErrorMetadata,
	PalletEventMetadata, PalletMetadata, PalletStorageMetadata, RuntimeMetadataV14,
	SignedExtensionMetadata, StorageEntryMetadata, StorageEntryModifier, StorageEntryType,
	StorageHasher,
};

impl From<MetadataIR> for RuntimeMetadataV14 {
	fn from(ir: MetadataIR) -> Self {
		RuntimeMetadataV14::new(
			ir.pallets.into_iter().map(Into::into).collect(),
			ir.extrinsic.into(),
			ir.ty,
		)
	}
}

impl From<PalletMetadataIR> for PalletMetadata {
	fn from(ir: PalletMetadataIR) -> Self {
		PalletMetadata {
			name: ir.name,
			storage: ir.storage.map(Into::into),
			calls: ir.calls.map(Into::into),
			event: ir.event.map(Into::into),
			constants: ir.constants.into_iter().map(Into::into).collect(),
			error: ir.error.map(Into::into),
			index: ir.index,
			// Note: ir.docs not part of v14.
		}
	}
}

impl From<StorageEntryModifierIR> for StorageEntryModifier {
	fn from(ir: StorageEntryModifierIR) -> Self {
		match ir {
			StorageEntryModifierIR::Optional => StorageEntryModifier::Optional,
			StorageEntryModifierIR::Default => StorageEntryModifier::Default,
		}
	}
}

impl From<StorageHasherIR> for StorageHasher {
	fn from(ir: StorageHasherIR) -> Self {
		match ir {
			StorageHasherIR::Blake2_128 => StorageHasher::Blake2_128,
			StorageHasherIR::Blake2_256 => StorageHasher::Blake2_256,
			StorageHasherIR::Blake2_128Concat => StorageHasher::Blake2_128Concat,
			StorageHasherIR::Twox128 => StorageHasher::Twox128,
			StorageHasherIR::Twox256 => StorageHasher::Twox256,
			StorageHasherIR::Twox64Concat => StorageHasher::Twox64Concat,
			StorageHasherIR::Identity => StorageHasher::Identity,
		}
	}
}

impl From<StorageEntryTypeIR> for StorageEntryType {
	fn from(ir: StorageEntryTypeIR) -> Self {
		match ir {
			StorageEntryTypeIR::Plain(ty) => StorageEntryType::Plain(ty),
			StorageEntryTypeIR::Map { hashers, key, value } => StorageEntryType::Map {
				hashers: hashers.into_iter().map(Into::into).collect(),
				key,
				value,
			},
		}
	}
}

impl From<StorageEntryMetadataIR> for StorageEntryMetadata {
	fn from(ir: StorageEntryMetadataIR) -> Self {
		StorageEntryMetadata {
			name: ir.name,
			modifier: ir.modifier.into(),
			ty: ir.ty.into(),
			default: ir.default,
			docs: ir.docs,
		}
	}
}

impl From<PalletStorageMetadataIR> for PalletStorageMetadata {
	fn from(ir: PalletStorageMetadataIR) -> Self {
		PalletStorageMetadata {
			prefix: ir.prefix,
			entries: ir.entries.into_iter().map(Into::into).collect(),
		}
	}
}

impl From<PalletCallMetadataIR> for PalletCallMetadata {
	fn from(ir: PalletCallMetadataIR) -> Self {
		PalletCallMetadata { ty: ir.ty }
	}
}

impl From<PalletEventMetadataIR> for PalletEventMetadata {
	fn from(ir: PalletEventMetadataIR) -> Self {
		PalletEventMetadata { ty: ir.ty }
	}
}

impl From<PalletConstantMetadataIR> for PalletConstantMetadata {
	fn from(ir: PalletConstantMetadataIR) -> Self {
		PalletConstantMetadata { name: ir.name, ty: ir.ty, value: ir.value, docs: ir.docs }
	}
}

impl From<PalletErrorMetadataIR> for PalletErrorMetadata {
	fn from(ir: PalletErrorMetadataIR) -> Self {
		PalletErrorMetadata { ty: ir.ty }
	}
}

impl From<SignedExtensionMetadataIR> for SignedExtensionMetadata {
	fn from(ir: SignedExtensionMetadataIR) -> Self {
		SignedExtensionMetadata {
			identifier: ir.identifier,
			ty: ir.ty,
			additional_signed: ir.additional_signed,
		}
	}
}

impl From<ExtrinsicMetadataIR> for ExtrinsicMetadata {
	fn from(ir: ExtrinsicMetadataIR) -> Self {
		ExtrinsicMetadata {
			ty: ir.ty,
			version: ir.version,
			signed_extensions: ir.signed_extensions.into_iter().map(Into::into).collect(),
		}
	}
}