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

//! Convert the IR to specific versions.

use super::types::MetadataIR;
#[cfg(feature = "metadata-v14")]
use frame_metadata::v14::RuntimeMetadataV14;
use frame_metadata::RuntimeMetadataPrefixed;

const V14: u32 = 14;

/// Transform the IR to the specified version.
///
/// Use [`supported_versions`] to find supported versions.
pub fn to_version(metadata: MetadataIR, version: u32) -> Option<RuntimeMetadataPrefixed> {
	match version {
		#[cfg(feature = "metadata-v14")]
		V14 => {
			let v14: RuntimeMetadataV14 = metadata.into();
			Some(v14.into())
		},
		_ => None,
	}
}

/// Returns the supported versions of metadata.
pub fn supported_versions() -> sp_std::vec::Vec<u32> {
	sp_std::vec![
		#[cfg(feature = "metadata-v14")]
		V14,
	]
}

#[cfg(test)]
mod test {
	use super::*;
	use crate::metadata_ir::ExtrinsicMetadataIR;
	#[cfg(feature = "metadata-v14")]
	use frame_metadata::v14::META_RESERVED;
	use frame_metadata::RuntimeMetadata;
	use scale_info::meta_type;

	fn ir_metadata() -> MetadataIR {
		MetadataIR {
			pallets: vec![],
			extrinsic: ExtrinsicMetadataIR {
				ty: meta_type::<()>(),
				version: 0,
				signed_extensions: vec![],
			},
			ty: meta_type::<()>(),
		}
	}

	#[test]
	fn to_version_14() {
		let ir = ir_metadata();
		let metadata = to_version(ir, V14).expect("Should return prefixed metadata");

		assert_eq!(metadata.0, META_RESERVED);

		assert!(matches!(metadata.1, RuntimeMetadata::V14(_)));
	}
}
