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

//! Defines WASM module logic.

use parachain::{self, ValidationResult};
use parachain::codec::Slicable;
use super::{HeadData, BlockData};

#[lang = "panic_fmt"]
#[no_mangle]
pub extern fn panic_fmt(
	_args: ::core::fmt::Arguments,
	_file: &'static str,
	_line: u32,
	_col: u32,
) -> ! {
	use core::intrinsics;
	unsafe {
		intrinsics::abort();
	}
}

#[no_mangle]
pub extern fn validate(offset: usize, len: usize) -> usize {
	let hash_state = |state: u64| ::tiny_keccak::keccak256(state.encode().as_slice());

	let params = unsafe { ::parachain::load_params(offset, len) };
	let parent_head = HeadData::decode(&mut &params.parent_head[..])
		.expect("invalid parent head format.");

	let block_data = BlockData::decode(&mut &params.block_data[..])
		.expect("invalid block data format.");

	assert_eq!(hash_state(block_data.state), parent_head.post_state, "wrong post-state proof");
	let new_state = block_data.state.saturating_add(block_data.add);

	let new_head = HeadData {
		number: parent_head.number + 1,
		parent_hash: ::tiny_keccak::keccak256(&params.parent_head[..]),
		post_state: hash_state(new_state),
	};

	parachain::write_result(ValidationResult { head_data: new_head.encode() })
}
