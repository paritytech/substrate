// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Simple ECDSA secp256k1 API. This is a reduced version of `sp_core::crypto::ecdsa` for use in
//! cases where the performance penalty of doing in-runtime crypto isn't severe. In case this
//! becomes a performance bottleneck a new host function should be considered.
use sp_core::{crypto::ByteArray, ecdsa::Public};

/// Extension trait for `sp_core::ecdsa::Public` to be used from inside runtime.
pub trait RuntimeECDSA {
	/// Returns Ethereum address calculated from this ECDSA public key.
	fn to_eth_address(&self) -> Result<[u8; 20], ()>;
}

impl RuntimeECDSA for Public {
	fn to_eth_address(&self) -> Result<[u8; 20], ()> {
		use k256::{elliptic_curve::sec1::ToEncodedPoint, PublicKey};

		PublicKey::from_sec1_bytes(self.as_slice())
			.map(|pub_key| {
				// uncompress the key
				let uncompressed = pub_key.to_encoded_point(false);
				// convert to ETH address
				let res: [u8; 20] = sp_io::hashing::keccak_256(&uncompressed.as_bytes()[1..])[12..]
					.try_into()
					.unwrap();
				res
			})
			.map_err(|_| ())
	}
}
