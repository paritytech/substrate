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
extern crate ed25519;

use std::collections::HashMap;
use ed25519::{Pair, Public, Signature};

/// Set of test accounts.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
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
		AsRef::<Pair>::as_ref(&self).sign(msg)
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
			Keyring::One => "one",
			Keyring::Two => "two",
		}
	}
}

lazy_static! {
	static ref PRIVATE_KEYS: HashMap<Keyring, Pair> = {
		let mut m = HashMap::new();
		m.insert(Keyring::Alice,	Pair::from_seed(b"Alice                           "));
		m.insert(Keyring::Bob,		Pair::from_seed(b"Bob                             "));
		m.insert(Keyring::Charlie,	Pair::from_seed(b"Charlie                         "));
		m.insert(Keyring::Dave,		Pair::from_seed(b"Dave                            "));
		m.insert(Keyring::Eve,		Pair::from_seed(b"Eve                             "));
		m.insert(Keyring::Ferdie,	Pair::from_seed(b"Ferdie                          "));
		m.insert(Keyring::One,		Pair::from_seed(b"12345678901234567890123456789012"));
		m.insert(Keyring::Two,		Pair::from_seed(&hex!("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")));
		m
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

impl AsRef<[u8]> for Keyring {
	fn as_ref(&self) -> &[u8] {
		(*PUBLIC_KEYS).get(self).unwrap().as_array_ref()
	}
}

impl AsRef<Public> for Keyring {
	fn as_ref(&self) -> &Public {
		(*PUBLIC_KEYS).get(self).unwrap()
	}
}

impl AsRef<Pair> for Keyring {
	fn as_ref(&self) -> &Pair {
		(*PRIVATE_KEYS).get(self).unwrap()
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
