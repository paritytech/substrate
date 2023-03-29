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

//! BLS12-381 crypto applications.

use crate::{KeyTypeId, RuntimePublic};

use sp_std::vec::Vec;

pub use sp_core::bls::bls381::*;

mod app {
	use sp_core::testing::BLS381;

	crate::app_crypto!(super, BLS381);

	impl crate::traits::BoundToRuntimeAppPublic for Public {
		type Public = Self;
	}
}

#[cfg(feature = "full_crypto")]
pub use app::Pair as AppPair;
pub use app::{Public as AppPublic, Signature as AppSignature};

impl RuntimePublic for Public {
	type Signature = Signature;

	fn all(_key_type: KeyTypeId) -> crate::Vec<Self> {
		unreachable!("no access to the host keystore from runtime")
	}

	fn generate_pair(_key_type: KeyTypeId, _seed: Option<Vec<u8>>) -> Self {
		unreachable!("no access to the host keystore from runtime")
	}

	fn sign<M: AsRef<[u8]>>(&self, _key_type: KeyTypeId, _msg: &M) -> Option<Self::Signature> {
		unreachable!("no access to the host keystore from runtime")
	}

	fn verify<M: AsRef<[u8]>>(&self, _msg: &M, _signature: &Self::Signature) -> bool {
		unreachable!("no access to the host keystore from runtime")
	}

	fn to_raw_vec(&self) -> Vec<u8> {
		sp_core::crypto::ByteArray::to_raw_vec(self)
	}
}
