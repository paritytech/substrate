// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Tool for creating the genesis block.

use std::collections::HashMap;
use runtime_io::twox_128;
use runtime_support::Hashable;
use codec::{KeyedVec, Joiner};
use primitives::AuthorityId;
use primitives::block::Block;

/// Configuration of a general Substrate test genesis block.
pub struct GenesisConfig {
	pub authorities: Vec<AuthorityId>,
	pub balances: Vec<(AuthorityId, u64)>,
}

impl GenesisConfig {
	pub fn new_simple(authorities: Vec<AuthorityId>, balance: u64) -> Self {
		GenesisConfig {
			authorities: authorities.clone(),
			balances: authorities.into_iter().map(|a| (a, balance)).collect(),
		}
	}

	pub fn genesis_map(&self) -> HashMap<Vec<u8>, Vec<u8>> {
		let wasm_runtime = include_bytes!("../wasm/genesis.wasm").to_vec();
		self.balances.iter()
			.map(|&(account, balance)| (account.to_keyed_vec(b"balance:"), vec![].and(&balance)))
			.map(|(k, v)| (twox_128(&k[..])[..].to_vec(), v.to_vec()))
			.chain(vec![
				(b":code"[..].into(), wasm_runtime),
				(b":auth:len"[..].into(), vec![].and(&(self.authorities.len() as u32))),
			].into_iter())
			.chain(self.authorities.iter()
				.enumerate()
				.map(|(i, account)| ((i as u32).to_keyed_vec(b":auth:"), vec![].and(account)))
			)
			.collect()
	}
}

macro_rules! map {
	($( $name:expr => $value:expr ),*) => (
		vec![ $( ( $name, $value ) ),* ].into_iter().collect()
	)
}

pub fn additional_storage_with_genesis(genesis_block: &Block) -> HashMap<Vec<u8>, Vec<u8>> {
	use codec::Slicable;
	map![
		twox_128(&b"latest"[..]).encode() => genesis_block.header.blake2_256().encode()
	]
}
