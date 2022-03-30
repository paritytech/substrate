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

//! Simple ECDSA secp256k1 API. Reduced version of such from sp_core to use in contracts.
use sp_core::{crypto::UncheckedFrom, ByteArray};

/// The ECDSA compressed public key.
pub struct Public(pub [u8; 33]);

impl Public {
	/// Converts self into Ethereum address
	pub fn to_eth_address(&self) -> Result<[u8; 20], ()> {
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

impl ByteArray for Public {
	const LEN: usize = 33;
}

impl AsRef<[u8]> for Public {
	fn as_ref(&self) -> &[u8] {
		&self.0[..]
	}
}

impl AsMut<[u8]> for Public {
	fn as_mut(&mut self) -> &mut [u8] {
		&mut self.0[..]
	}
}

impl sp_std::convert::TryFrom<&[u8]> for Public {
	type Error = ();

	fn try_from(data: &[u8]) -> Result<Self, Self::Error> {
		if data.len() != Self::LEN {
			return Err(())
		}
		let mut r = [0u8; Self::LEN];
		r.copy_from_slice(data);
		Ok(Self::unchecked_from(r))
	}
}

impl UncheckedFrom<[u8; 33]> for Public {
	fn unchecked_from(x: [u8; 33]) -> Self {
		Public(x)
	}
}
