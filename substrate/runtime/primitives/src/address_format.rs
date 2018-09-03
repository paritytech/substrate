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

use byte_num::convert::IntoAscii;
use testing::Digest;
use substrate_primitives::H256;
use generic::Digest as GenericDigest;
use ed25519::Public;

#[derive(Clone, Debug)]
pub struct SS58Compatible ( pub Public);

pub trait SS58: Into<SS58Compatible > {
    fn encode(self) -> String {
        self.into().0.to_ss58check()
    }
}

impl From<u64> for SS58Compatible {
    fn from(x: u64) -> Self {
        SS58Compatible (Public::from_slice(&x.itoa()))
    }
}

impl SS58 for u64 {}

impl From<Digest> for SS58Compatible {
    fn from(x: Digest) -> Self {
        SS58Compatible (Public::from_slice(&x
            .logs
            .iter()
            .map(|digest| digest.itoa())
            .flatten()
            .collect::<Vec<u8>>()
        ))
    }
}
impl SS58 for Digest {}

impl From<H256> for SS58Compatible {
    fn from(x: H256) -> Self {
        SS58Compatible (Public::from_slice(&x[..]))
    }
}

impl SS58 for H256 {}

impl<Item: Into<u8>> From<GenericDigest<Item>> for SS58Compatible where
    Vec<u8> : From<Vec<Item>>
{
    fn from(x: GenericDigest<Item>) -> Self {
        SS58Compatible (Public::from_slice(Vec::from(x.logs).as_slice()))
    }
}

impl<Item: Into<u8>> SS58 for GenericDigest<Item> where
    Vec<u8>: From<Vec<Item>>
{}

impl<Item: Into<u8>> From<GenericDigest<Item>> for Vec<u8>
{
    fn from(x: GenericDigest<Item>) -> Self {
        x.logs.into_iter().map(|element| Into::<u8>::into(element)).collect()
    }

}
