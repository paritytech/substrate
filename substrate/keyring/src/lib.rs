// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Support code for the runtime.

#[macro_use] extern crate hex_literal;
#[macro_use] extern crate lazy_static;
pub extern crate ed25519;

use std::collections::HashMap;
use std::ops::Deref;
use ed25519::{Pair, Public, Signature};

/// Set of test accounts.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Keyring {
	None,
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
	pub fn from_public(who: Public) -> Option<Keyring> {
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
			.find(|&k| Public::from(k) == who)
	}

	pub fn from_raw_public(who: [u8; 32]) -> Option<Keyring> {
		Self::from_public(Public::from_raw(who))
	}

	pub fn to_raw_public(self) -> [u8; 32] {
		*Public::from(self).as_array_ref()
	}

	pub fn to_raw_public_vec(self) -> Vec<u8> {
		Public::from(self).to_raw_vec()
	}

	pub fn sign(self, msg: &[u8]) -> Signature {
		Pair::from(self).sign(msg)
	}

	pub fn pair(self) -> Pair {
		match self {
			Keyring::None => { panic!(); },
			Keyring::Alice => Pair::from_seed(b"Alice                           "),
			Keyring::Bob => Pair::from_seed(b"Bob                             "),
			Keyring::Charlie => Pair::from_seed(b"Charlie                         "),
			Keyring::Dave => Pair::from_seed(b"Dave                            "),
			Keyring::Eve => Pair::from_seed(b"Eve                             "),
			Keyring::Ferdie => Pair::from_seed(b"Ferdie                          "),
			Keyring::One => Pair::from_seed(b"12345678901234567890123456789012"),
			Keyring::Two => Pair::from_seed(&hex!("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")),
		}
	}
}

impl From<Keyring> for &'static str {
	fn from(k: Keyring) -> Self {
		match k {
			Keyring::None => { panic!(); },
			Keyring::Alice => "Alice",
			Keyring::Bob => "Bob",
			Keyring::Charlie => "Charlie",
			Keyring::Dave => "Dave",
			Keyring::Eve => "Eve",
			Keyring::Ferdie => "Ferdie",
			Keyring::One => "one",
			Keyring::Two => "two",
		}
	}
}

impl From<Keyring> for u64 {
	fn from(k: Keyring) -> Self {
		match k {
			Keyring::None => 0,
			Keyring::Alice => 1,
			Keyring::Bob => 2,
			Keyring::Charlie => 3,
			Keyring::Dave => 4,
			Keyring::Eve => 5,
			Keyring::Ferdie => 6,
			Keyring::One => 7,
			Keyring::Two => 8,
		}
	}
}

impl From<u64> for Keyring {
	fn from(k: u64) -> Keyring {
		match k {
			1 => Keyring::Alice,
			2 => Keyring::Bob,
			3 => Keyring::Charlie,
			4 => Keyring::Dave,
			5 => Keyring::Eve,
			6 => Keyring::Ferdie,
			7 => Keyring::One,
			8 => Keyring::Two,
			_ => Keyring::None,
		}
	}
}

lazy_static! {
	static ref PRIVATE_KEYS: HashMap<Keyring, Pair> = {
		[
			Keyring::Alice,
			Keyring::Bob,
			Keyring::Charlie,
			Keyring::Dave,
			Keyring::Eve,
			Keyring::Ferdie,
			Keyring::One,
			Keyring::Two,
		].iter().map(|&i| (i, i.pair())).collect()
	};

	static ref PUBLIC_KEYS: HashMap<Keyring, Public> = {
		let mut m: HashMap<_, _> = PRIVATE_KEYS.iter().map(|(&name, pair)| (name, pair.public())).collect();
		m.insert(Keyring::None, Public(Default::default()));
		m
	};

	static ref U64_KEYS: HashMap<Keyring, u64> = {
		(0u64..9).map(|n| (n.into(), n)).collect()
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

impl AsRef<u64> for Keyring {
	fn as_ref(&self) -> &u64 {
		(*U64_KEYS).get(self).unwrap()
	}
}

impl AsRef<Public> for Keyring {
	fn as_ref(&self) -> &Public {
		(*PUBLIC_KEYS).get(self).unwrap()
	}
}

impl Deref for Keyring {
	type Target = u64;
	fn deref(&self) -> &u64 {
		(*U64_KEYS).get(self).unwrap()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use ed25519::Verifiable;

	#[test]
	fn should_work() {
		assert!(Keyring::Alice.sign(b"I am Alice!").verify(b"I am Alice!", Keyring::Alice));
		assert!(!Keyring::Alice.sign(b"I am Alice!").verify(b"I am Bob!", Keyring::Alice));
		assert!(!Keyring::Alice.sign(b"I am Alice!").verify(b"I am Alice!", Keyring::Bob));
	}
}
