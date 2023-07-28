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

//! Intermediate representation of the runtime metadata.

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

// Re-export.
#[doc(hidden)]
pub use frame_metadata;

mod types;
use frame_metadata::RuntimeMetadataPrefixed;
pub use types::*;

mod v14;
mod v15;

/// Metadata V14.
const V14: u32 = 14;

/// Metadata V15.
const V15: u32 = 15;

/// Transform the IR to the specified version.
///
/// Use [`supported_versions`] to find supported versions.
pub fn into_version(metadata: MetadataIR, version: u32) -> Option<RuntimeMetadataPrefixed> {
	// Note: Unstable metadata version is `u32::MAX` until stabilized.
	match version {
		// Latest stable version.
		V14 => Some(into_v14(metadata)),
		// Unstable metadata.
		V15 => Some(into_latest(metadata)),
		_ => None,
	}
}

/// Returns the supported metadata versions.
pub fn supported_versions() -> sp_std::vec::Vec<u32> {
	sp_std::vec![V14, V15]
}

/// Transform the IR to the latest stable metadata version.
pub fn into_latest(metadata: MetadataIR) -> RuntimeMetadataPrefixed {
	let latest: frame_metadata::v15::RuntimeMetadataV15 = metadata.into();
	latest.into()
}

/// Transform the IR to metadata version 14.
pub fn into_v14(metadata: MetadataIR) -> RuntimeMetadataPrefixed {
	let latest: frame_metadata::v14::RuntimeMetadataV14 = metadata.into();
	latest.into()
}

#[cfg(test)]
mod test {
	use super::*;
	use frame_metadata::{v14::META_RESERVED, RuntimeMetadata};
	use scale_info::meta_type;

	fn ir_metadata() -> MetadataIR {
		MetadataIR {
			pallets: vec![],
			extrinsic: ExtrinsicMetadataIR {
				ty: meta_type::<()>(),
				version: 0,
				address_ty: meta_type::<()>(),
				call_ty: meta_type::<()>(),
				signature_ty: meta_type::<()>(),
				extra_ty: meta_type::<()>(),
				signed_extensions: vec![],
			},
			ty: meta_type::<()>(),
			apis: vec![],
			outer_enums: OuterEnumsIR {
				call_enum_ty: meta_type::<()>(),
				event_enum_ty: meta_type::<()>(),
				error_enum_ty: meta_type::<()>(),
			},
		}
	}

	#[test]
	fn into_version_14() {
		let ir = ir_metadata();
		let metadata = into_version(ir, V14).expect("Should return prefixed metadata");

		assert_eq!(metadata.0, META_RESERVED);

		assert!(matches!(metadata.1, RuntimeMetadata::V14(_)));
	}

	#[test]
	fn into_version_15() {
		let ir = ir_metadata();
		let metadata = into_version(ir, V15).expect("Should return prefixed metadata");

		assert_eq!(metadata.0, META_RESERVED);

		assert!(matches!(metadata.1, RuntimeMetadata::V15(_)));
	}
}
