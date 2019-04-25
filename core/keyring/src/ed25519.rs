// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Support code for the runtime. A set of test accounts.

use std::{collections::HashMap, ops::Deref};
use lazy_static::lazy_static;
use substrate_primitives::{ed25519::{Pair, Public, Signature}, Pair as PairT, H256};
pub use substrate_primitives::ed25519;

/// Set of test accounts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, strum_macros::Display, strum_macros::EnumIter)]
pub enum Keyring {
	Alice,
	Bob,
	Charlie,
	Dave,
	Eve,
	Ferdie,
	One,
	Two,
}

impl Keyring {
	pub fn from_public(who: &Public) -> Option<Keyring> {
		[
			Keyring::Alice,
			Keyring::Bob,
			Keyring::Charlie,
			Keyring::Dave,
			Keyring::Eve,
			Keyring::Ferdie,
			Keyring::One,
			Keyring::Two,
		].iter()
			.map(|i| *i)
			.find(|&k| &Public::from(k) == who)
	}

	pub fn from_raw_public(who: [u8; 32]) -> Option<Keyring> {
		Self::from_public(&Public::from_raw(who))
	}

	pub fn to_raw_public(self) -> [u8; 32] {
		*Public::from(self).as_array_ref()
	}

	pub fn from_h256_public(who: H256) -> Option<Keyring> {
		Self::from_public(&Public::from_raw(who.into()))
	}

	pub fn to_h256_public(self) -> H256 {
		Public::from(self).as_array_ref().into()
	}

	pub fn to_raw_public_vec(self) -> Vec<u8> {
		Public::from(self).to_raw_vec()
	}

	pub fn sign(self, msg: &[u8]) -> Signature {
		Pair::from(self).sign(msg)
	}

	pub fn pair(self) -> Pair {
		Pair::from_string(&format!("//{}", <&'static str>::from(self)), None)
			.expect("static values are known good; qed")
	}

	/// Returns an interator over all test accounts.
	pub fn iter() -> impl Iterator<Item=Keyring> {
		<Self as strum::IntoEnumIterator>::iter()
	}
}

impl From<Keyring> for &'static str {
	fn from(k: Keyring) -> Self {
		match k {
			Keyring::Alice => "Alice",
			Keyring::Bob => "Bob",
			Keyring::Charlie => "Charlie",
			Keyring::Dave => "Dave",
			Keyring::Eve => "Eve",
			Keyring::Ferdie => "Ferdie",
			Keyring::One => "One",
			Keyring::Two => "Two",
		}
	}
}

lazy_static! {
	static ref PRIVATE_KEYS: HashMap<Keyring, Pair> = {
		Keyring::iter().map(|i| (i, i.pair())).collect()
	};

	static ref PUBLIC_KEYS: HashMap<Keyring, Public> = {
		PRIVATE_KEYS.iter().map(|(&name, pair)| (name, pair.public())).collect()
	};
}

impl From<Keyring> for Public {
	fn from(k: Keyring) -> Self {
		(*PUBLIC_KEYS).get(&k).unwrap().clone()
	}
}

impl From<Keyring> for Pair {
	fn from(k: Keyring) -> Self {
		k.pair()
	}
}

impl From<Keyring> for [u8; 32] {
	fn from(k: Keyring) -> Self {
		*(*PUBLIC_KEYS).get(&k).unwrap().as_array_ref()
	}
}

impl From<Keyring> for H256 {
	fn from(k: Keyring) -> Self {
		(*PUBLIC_KEYS).get(&k).unwrap().as_array_ref().into()
	}
}

impl From<Keyring> for &'static [u8; 32] {
	fn from(k: Keyring) -> Self {
		(*PUBLIC_KEYS).get(&k).unwrap().as_array_ref()
	}
}

impl AsRef<[u8; 32]> for Keyring {
	fn as_ref(&self) -> &[u8; 32] {
		(*PUBLIC_KEYS).get(self).unwrap().as_array_ref()
	}
}

impl AsRef<Public> for Keyring {
	fn as_ref(&self) -> &Public {
		(*PUBLIC_KEYS).get(self).unwrap()
	}
}

impl Deref for Keyring {
	type Target = [u8; 32];
	fn deref(&self) -> &[u8; 32] {
		(*PUBLIC_KEYS).get(self).unwrap().as_array_ref()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use substrate_primitives::{ed25519::Pair, Pair as PairT};

	#[test]
	fn should_work() {
		assert!(Pair::verify(&Keyring::Alice.sign(b"I am Alice!"), b"I am Alice!", Keyring::Alice));
		assert!(!Pair::verify(&Keyring::Alice.sign(b"I am Alice!"), b"I am Bob!", Keyring::Alice));
		assert!(!Pair::verify(&Keyring::Alice.sign(b"I am Alice!"), b"I am Alice!", Keyring::Bob));
	}
}
