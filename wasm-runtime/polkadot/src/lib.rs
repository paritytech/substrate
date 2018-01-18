#![cfg_attr(feature = "without-std", no_std)]
#![cfg_attr(feature = "strict", deny(warnings))]

#[macro_use]
extern crate runtime_support;

#[cfg(test)]
extern crate rustc_hex;

mod codec;
mod support;
mod runtime;
pub use codec::{endiansensitive, streamreader, joiner, slicable, keyedvec};
pub use support::{primitives, function, environment, storage};
#[cfg(test)]
pub use support::{testing, statichex};


#[allow(unused_imports)]		// TODO: remove in due course
use runtime_support::Vec;
use slicable::Slicable;
use primitives::{Block, UncheckedTransaction};

// TODO: add externals for:
// - trie rooting

pub fn execute_block(input: Vec<u8>) -> Vec<u8> {
	runtime::system::execute_block(Block::from_slice(&input).unwrap());
	Vec::new()
}

pub fn execute_transaction(input: Vec<u8>) -> Vec<u8> {
	runtime::system::execute_transaction(&UncheckedTransaction::from_slice(&input).unwrap());
	Vec::new()
}

impl_stubs!(execute_block, execute_transaction);
