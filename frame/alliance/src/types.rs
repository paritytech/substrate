// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//  http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use codec::{Decode, Encode, EncodeLike, Error, Input, Output};
use sp_runtime::RuntimeDebug;
use sp_std::{ops::Deref, vec};

/// A wrapped Cid for source Cid struct, to implement a valid encode/decode for Cid.
///
/// This file will be used until this pr is merged:
/// https://github.com/multiformats/rust-multihash/pull/116
/// For now, the source Cid use a static length `U64(H256)` for all Cid type, if we use the source
/// Cid encode/decode, it will add lots of empty zero in the result.
///
/// e.g.
/// In the most widely used Cid type in IPFS, like:
/// QmRZdc3mAMXpv6Akz9Ekp1y4vDSjazTx2dCQRkxVy1yUj6
/// If we use the source Cid to do encode, it will be:
/// 00-7000000000000000-1200000000000000-20-2fe65ccc17fe180c3bf4e9b8490fcc6dc74c30bf6595795dcd1136d8d9cb3f950000000000000000000000000000000000000000000000000000000000000000
/// |Version|-|codec:u64|-|MultiHash|
///                       |codec:u64| - |size:u8| - |digest|
/// We can see that ths digest part contains lots of zero for current digest in MultiHash is `[u8;
/// 64]`, However the generic hash length is 32. So the default encode/decode method wastes a lot of
/// space.
///
/// And in pr#116 which is list above, the static length will be changed for multihash. Thus the
/// encode/decode method will be suitable for different Cid type.
/// So we consider this pr, decide to implement a encode/decode method for Cid which will be
/// **compatible** with the modification in pr#116.
///
/// In our encode/decode, for the last part `digest`, we write the **raw value** to buffer and
/// read it from buffer **directly**, and do not add other byte like hint size or else.
/// The `code` and `size` is encoded/decoded in normal way.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, RuntimeDebug)]
pub struct Cid(cid::Cid);

impl Cid {
	pub fn new(cid: cid::Cid) -> Self {
		Self(cid)
	}
}

impl Encode for Cid {
	fn encode_to<EncOut: Output + ?Sized>(&self, dest: &mut EncOut) {
		// for cid
		self.version().encode_to(dest);
		self.codec().encode_to(dest);
		// for multihash
		let hash = self.hash();
		let code = hash.code();
		let size = hash.size();
		let digest = hash.digest();

		code.encode_to(dest);
		size.encode_to(dest);
		// notice we write the digest directly to dest, for we have known the size.
		// **IMPORTANT**
		// we do not choose to encode &[u8] directly, for it will add compact length at start.
		//
		// in a valid cid, digest.len() must equal to `size`. Thus, in Decode,
		// we can just read a raw bytes which length is equal to `size`.
		dest.write(digest)
	}
}

impl EncodeLike for Cid {}

impl Decode for Cid {
	fn decode<I: Input>(input: &mut I) -> Result<Self, Error> {
		use cid::{
			multihash::{MultihashGeneric, U64},
			Version,
		};

		type Multihash = MultihashGeneric<U64>;

		// for cid
		let version: Version = Decode::decode(input)?;
		let codec: u64 = Decode::decode(input)?;
		// for multihash
		let code: u64 = Decode::decode(input)?;
		let size: u8 = Decode::decode(input)?;
		let mut buf = vec![0; size as usize];
		// In a valid Cid, the size must equal to this raw buffer.
		input.read(&mut buf)?;
		let hash = Multihash::wrap(code, &buf).map_err(|_| "Multihash parse error")?;
		Ok(Cid::new(cid::Cid::new(version, codec, hash).map_err(|_| "Cid parse error")?))
	}
}

impl Into<cid::Cid> for Cid {
	fn into(self) -> cid::Cid {
		self.0
	}
}

impl From<cid::Cid> for Cid {
	fn from(cid: cid::Cid) -> Self {
		Cid::new(cid)
	}
}

impl AsRef<cid::Cid> for Cid {
	fn as_ref(&self) -> &cid::Cid {
		&self.0
	}
}

impl AsMut<cid::Cid> for Cid {
	fn as_mut(&mut self) -> &mut cid::Cid {
		&mut self.0
	}
}

impl Deref for Cid {
	type Target = cid::Cid;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use cid::{
		multibase::Base,
		multihash::{Code, MultihashDigest},
		Version,
	};
	use sp_std::{convert::TryFrom, str::FromStr};

	const RAW: u64 = 0x55;

	#[test]
	fn normal_test_for_example() {
		let s = "QmRZdc3mAMXpv6Akz9Ekp1y4vDSjazTx2dCQRkxVy1yUj6";
		let cid: Cid = cid::Cid::from_str(s).expect("must be valid.").into();
		let bytes = cid.encode();
		let expect = hex_literal::hex!("0070000000000000001200000000000000202fe65ccc17fe180c3bf4e9b8490fcc6dc74c30bf6595795dcd1136d8d9cb3f95");
		assert_eq!(bytes, expect);
		let new_cid: Cid = Decode::decode(&mut &bytes[..]).expect("must decode well");
		assert_eq!(new_cid, cid);
	}

	macro_rules! assert_cid {
		($cid:expr, $length:expr) => {
			let mut digest = [0_u8; $length];
			digest.copy_from_slice($cid.hash().digest());
			let raw =
				($cid.version(), $cid.codec(), ($cid.hash().code(), $cid.hash().size(), digest));
			let raw_encode = Encode::encode(&raw);
			let bytes = $cid.encode();
			assert_eq!(bytes, raw_encode);
			let new_cid: Cid = Decode::decode(&mut &bytes[..]).expect("must decode well");
			assert_eq!(new_cid, $cid);
		};
	}
	// those test case is from crate rust-cid
	#[test]
	fn v0_handling() {
		let old = "QmdfTbBqBPQ7VNxZEYEj14VmRuZBkqFbiwReogJgS1zR1n";
		let cid: Cid = cid::Cid::try_from(old).expect("must be valid.").into();

		assert_eq!(cid.version(), Version::V0);
		assert_eq!(cid.to_string(), old);

		// for Cid v0 hash is 32 length
		assert_cid!(cid, 32);
	}

	#[test]
	fn v1_handling() {
		let expected_cid = "bafkreibme22gw2h7y2h7tg2fhqotaqjucnbc24deqo72b6mkl2egezxhvy";
		let cid: Cid = cid::Cid::new_v1(RAW, Code::Sha2_256.digest(b"foo")).into();
		assert_eq!(cid.to_string_of_base(Base::Base32Lower).unwrap(), expected_cid);

		// for sha256 hash is 32 length
		assert_cid!(cid, 32);
	}

	// test case from https://github.com/ipfs/go-cid/blob/master/cid_test.go#L662
	#[test]
	fn v1_handling2() {
		let cid1: Cid =
			cid::Cid::from_str("k2cwueckqkibutvhkr4p2ln2pjcaxaakpd9db0e7j7ax1lxhhxy3ekpv")
				.expect("must valid")
				.into();
		let cid2: Cid = cid::Cid::from_str("zb2rhZi1JR4eNc2jBGaRYJKYM8JEB4ovenym8L1CmFsRAytkz")
			.expect("must valid")
			.into();
		assert_cid!(cid1, 32);
		assert_cid!(cid2, 32);
	}

	#[test]
	fn v1_handling3() {
		let cid: Cid = cid::Cid::new_v1(RAW, Code::Sha2_512.digest(b"foo")).into();
		assert_cid!(cid, 64);

		let cid: Cid = cid::Cid::new_v1(RAW, Code::Keccak384.digest(b"foo")).into();
		assert_cid!(cid, 48);

		let cid: Cid = cid::Cid::new_v1(RAW, Code::Sha3_224.digest(b"foo")).into();
		assert_cid!(cid, 28);

		let cid: Cid = cid::Cid::new_v1(RAW, Code::Blake2s128.digest(b"foo")).into();
		assert_cid!(cid, 16);
	}
}
