#![cfg_attr(feature = "without-std", no_std)]
#![cfg_attr(feature = "strict", deny(warnings))]

#[macro_use]
extern crate runtime_support;

mod support;
pub use support::{endiansensitive, streamreader, joiner, slicable, primitives, keyedvec, function,
	environment, storage};
#[cfg(test)]
pub use support::testing;

#[allow(unused)]
mod system;
#[allow(unused)]
mod consensus;
#[allow(unused)]
mod staking;
#[allow(unused)]
mod timestamp;

use runtime_support::Vec;
use slicable::Slicable;
use primitives::{Block, Transaction};

// TODO: add externals for:
// - keccak256 (or some better hashing scheme)
// - trie rooting
// - ECDSA-recover (or some better sig scheme)

pub fn execute_block(input: Vec<u8>) -> Vec<u8> {
	system::execute_block(Block::from_slice(&input).unwrap())
}

pub fn execute_transaction(input: Vec<u8>) -> Vec<u8> {
	system::execute_transaction(&Transaction::from_slice(&input).unwrap())
}

impl_stubs!(execute_block, execute_transaction);
