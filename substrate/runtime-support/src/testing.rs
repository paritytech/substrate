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

//! Testing helpers.

use primitives::AuthorityId;
use ed25519::{Pair, Public};

/// Set of test accounts.
#[derive(Clone, Copy, PartialEq)]
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

impl From<Keyring> for Pair {
	fn from(k: Keyring) -> Self {
		match k {
			Keyring::Alice => 		Pair::from_seed(b"Alice                           "),
			Keyring::Bob => 		Pair::from_seed(b"Bob                             "),
			Keyring::Charlie => 	Pair::from_seed(b"Charlie                         "),
			Keyring::Dave => 		Pair::from_seed(b"Dave                            "),
			Keyring::Eve => 		Pair::from_seed(b"Eve                             "),
			Keyring::Ferdie => 		Pair::from_seed(b"Ferdie                          "),
			Keyring::One => 		Pair::from_seed(b"12345678901234567890123456789012"),
			Keyring::Two => 		Pair::from_seed(&hex!("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")),
		}
	}
}

impl From<Keyring> for Public {
	fn from(k: Keyring) -> Self {
		let pair: Pair = k.into();
		pair.public()
	}
}

/// One account (to which we know the secret key).
pub fn one() -> AuthorityId {
	hex!("2f8c6129d816cf51c374bc7f08c3e63ed156cf78aefb4a6550d97b87997977ee")
}
/// Another account (secret key known).
pub fn two() -> AuthorityId {
	hex!("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
}
