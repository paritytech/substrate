// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Support code for the runtime. A set of test accounts.

use lazy_static::lazy_static;
pub use sp_core::sr25519;
use sp_core::{
	sr25519::{Pair, Public, Signature},
	ByteArray, Pair as PairT, H256,
};
use sp_runtime::AccountId32;
use std::{collections::HashMap, ops::Deref};

/// Set of test accounts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, strum::Display, strum::EnumIter)]
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
		Self::iter().find(|&k| &Public::from(k) == who)
	}

	pub fn from_account_id(who: &AccountId32) -> Option<Keyring> {
		Self::iter().find(|&k| &k.to_account_id() == who)
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

	pub fn to_account_id(self) -> AccountId32 {
		self.to_raw_public().into()
	}

	pub fn sign(self, msg: &[u8]) -> Signature {
		Pair::from(self).sign(msg)
	}

	pub fn pair(self) -> Pair {
		Pair::from_string(&format!("//{}", <&'static str>::from(self)), None)
			.expect("static values are known good; qed")
	}

	/// Returns an iterator over all test accounts.
	pub fn iter() -> impl Iterator<Item = Keyring> {
		<Self as strum::IntoEnumIterator>::iter()
	}

	pub fn public(self) -> Public {
		self.pair().public()
	}

	pub fn to_seed(self) -> String {
		format!("//{}", self)
	}

	/// Create a crypto `Pair` from a numeric value.
	pub fn numeric(idx: usize) -> Pair {
		Pair::from_string(&format!("//{}", idx), None).expect("numeric values are known good; qed")
	}

	/// Get account id of a `numeric` account.
	pub fn numeric_id(idx: usize) -> AccountId32 {
		(*Self::numeric(idx).public().as_array_ref()).into()
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

impl From<Keyring> for sp_runtime::MultiSigner {
	fn from(x: Keyring) -> Self {
		sp_runtime::MultiSigner::Sr25519(x.into())
	}
}

#[derive(Debug)]
pub struct ParseKeyringError;

impl std::fmt::Display for ParseKeyringError {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "ParseKeyringError")
	}
}

impl std::str::FromStr for Keyring {
	type Err = ParseKeyringError;

	fn from_str(s: &str) -> Result<Self, <Self as std::str::FromStr>::Err> {
		match s {
			"alice" => Ok(Keyring::Alice),
			"bob" => Ok(Keyring::Bob),
			"charlie" => Ok(Keyring::Charlie),
			"dave" => Ok(Keyring::Dave),
			"eve" => Ok(Keyring::Eve),
			"ferdie" => Ok(Keyring::Ferdie),
			"one" => Ok(Keyring::One),
			"two" => Ok(Keyring::Two),
			_ => Err(ParseKeyringError),
		}
	}
}

lazy_static! {
	static ref PRIVATE_KEYS: HashMap<Keyring, Pair> =
		Keyring::iter().map(|i| (i, i.pair())).collect();
	static ref PUBLIC_KEYS: HashMap<Keyring, Public> =
		PRIVATE_KEYS.iter().map(|(&name, pair)| (name, pair.public())).collect();
}

impl From<Keyring> for AccountId32 {
	fn from(k: Keyring) -> Self {
		k.to_account_id()
	}
}

impl From<Keyring> for Public {
	fn from(k: Keyring) -> Self {
		*(*PUBLIC_KEYS).get(&k).unwrap()
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
	use sp_core::{sr25519::Pair, Pair as PairT};

	#[test]
	fn should_work() {
		assert!(Pair::verify(
			&Keyring::Alice.sign(b"I am Alice!"),
			b"I am Alice!",
			&Keyring::Alice.public(),
		));
		assert!(!Pair::verify(
			&Keyring::Alice.sign(b"I am Alice!"),
			b"I am Bob!",
			&Keyring::Alice.public(),
		));
		assert!(!Pair::verify(
			&Keyring::Alice.sign(b"I am Alice!"),
			b"I am Alice!",
			&Keyring::Bob.public(),
		));
	}
}
