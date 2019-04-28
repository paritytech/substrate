// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

	// need to prefix with the total length to ensure it's binary compatible with
	// Vec<u8>.
	let mut length: Vec<()> = Vec::new();
	length.resize(v.len() - reserve, ());
	length.using_encoded(|s| {
		v.splice(0..reserve, s.iter().cloned());
	});

	v
}
