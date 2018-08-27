// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

use base58::ToBase58;
use byte_num::convert::IntoAscii;
use testing::Digest;
use substrate_primitives::H256;
use generic::Digest as GenericDigest;


#[derive(Clone, Debug)]
pub struct Base58Compatible ( pub Vec<u8>);

pub trait Base58 : Into<Base58Compatible> {
    fn encode(self) -> String {
        self.into().0.to_base58()
    }
}

impl From<u64> for Base58Compatible {
    fn from(x: u64) -> Self {
        Base58Compatible(x.itoa())
    }
}

impl Base58 for u64 {}

impl From<Digest> for Base58Compatible {
    fn from(x: Digest) -> Self {
        Base58Compatible(x.logs.iter().map(|digest| digest.itoa()).flatten().collect())
    }
}
impl Base58 for Digest {}

impl From<H256> for Base58Compatible {
    fn from(x: H256) -> Self {
        Base58Compatible(x[..].to_vec())
    }
}

impl Base58 for H256 {}

impl<Item: Into<u8>> From<GenericDigest<Item>> for Base58Compatible where
    Vec<u8> : From<Vec<Item>>
{
    fn from(x: GenericDigest<Item>) -> Self {
        Base58Compatible(x.into())
    }
}

impl<Item: Into<u8>> Base58 for GenericDigest<Item> where
    Vec<u8>: From<Vec<Item>>
{}

impl<Item: Into<u8>> From<GenericDigest<Item>> for Vec<u8>
{
    fn from(x: GenericDigest<Item>) -> Self {
        x.logs.into_iter().map(|element| Into::<u8>::into(element)).collect()
    }

}
