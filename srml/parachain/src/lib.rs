// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! A module that enables a runtime to work as parachain.

#![cfg_attr(not(feature = "std"), no_std)]

use runtime_primitives::traits::{Block as BlockT, One, Header as HeaderT};
use rstd::{vec::Vec, collections::btree_map::BTreeMap, marker::PhantomData};
use executive::ExecuteBlock;
use parity_codec::Decode;
use parity_codec_derive::{Encode, Decode};

/// The parachain block that is created on a collator and validated by a validator.
#[derive(Encode, Decode)]
struct ParachainBlock<B: BlockT> {
	extrinsics: Vec<<B as BlockT>::Extrinsic>,
	/// The data that is required to emulate the storage accesses executed by all extrinsics.
	witness_data: Vec<(Vec<u8>, Vec<u8>)>,
}

pub struct Parachain<Block: BlockT, E: ExecuteBlock<Block>>(PhantomData<(Block, E)>);

impl<Block: BlockT, E: ExecuteBlock<Block>> Parachain<Block, E> {
	pub fn validate_block(block: Vec<u8>, prev_head: Vec<u8>) {
		let block = ParachainBlock::<Block>::decode(&mut &block[..]).expect("Could not decode parachain block.");
		let parent_header = <<Block as BlockT>::Header as Decode>::decode(&mut &prev_head[..]).expect("Could not decode parent header.");

		let block_number = *parent_header.number() + One::one();

		E::execute_extrinsics_without_checks(block_number, block.extrinsics);
	}
}

#[no_mangle]
fn validate_block(block: *const u8, block_len: u64, prev_head: *const u8, prev_head_len: u64) {

}