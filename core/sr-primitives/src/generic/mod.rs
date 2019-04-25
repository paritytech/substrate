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

// tag::description[]
//! Generic implementations of Extrinsic/Header/Block.
// end::description[]

mod unchecked_extrinsic;
mod unchecked_mortal_extrinsic;
mod unchecked_mortal_compact_extrinsic;
mod era;
mod checked_extrinsic;
mod header;
mod block;
mod digest;
#[cfg(test)]
mod tests;

pub use self::unchecked_extrinsic::UncheckedExtrinsic;
pub use self::unchecked_mortal_extrinsic::UncheckedMortalExtrinsic;
pub use self::unchecked_mortal_compact_extrinsic::UncheckedMortalCompactExtrinsic;
pub use self::era::Era;
pub use self::checked_extrinsic::CheckedExtrinsic;
pub use self::header::Header;
pub use self::block::{Block, SignedBlock, BlockId};
pub use self::digest::{Digest, DigestItem, DigestItemRef};

use crate::codec::Encode;
use rstd::prelude::*;

fn encode_with_vec_prefix<T: Encode, F: Fn(&mut Vec<u8>)>(encoder: F) -> Vec<u8> {
	let size = ::rstd::mem::size_of::<T>();
	let reserve = match size {
		0...0b00111111 => 1,
		0...0b00111111_11111111 => 2,
		_ => 4,
	};
	let mut v = Vec::with_capacity(reserve + size);
	v.resize(reserve, 0);
	encoder(&mut v);

	// need to prefix with the total length to ensure it's binary comptible with
	// Vec<u8>.
	let mut length: Vec<()> = Vec::new();
	length.resize(v.len() - reserve, ());
	length.using_encoded(|s| {
		v.splice(0..reserve, s.iter().cloned());
	});

	v
}
