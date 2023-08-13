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

//! Convert the IR to V14 metadata.

use super::types::{
	ExtrinsicMetadataIR, MetadataIR, PalletCallMetadataIR, PalletConstantMetadataIR,
	PalletErrorMetadataIR, PalletEventMetadataIR, PalletMetadataIR, PalletStorageMetadataIR,
	SignedExtensionMetadataIR, StorageEntryMetadataIR, StorageEntryModifierIR, StorageEntryTypeIR,
	StorageHasherIR,
};

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
