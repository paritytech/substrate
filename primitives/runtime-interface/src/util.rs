// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Various utilities that help interfacing with wasm runtime code.

/// Pack a pointer and length into an `u64`.
pub fn pack_ptr_and_len(ptr: u32, len: u32) -> u64 {
	// The static assertions from above are changed into a runtime check.
	#[cfg(all(not(feature = "std"), feature = "disable_target_static_assertions"))]
	assert_eq!(4, sp_std::mem::size_of::<usize>());

	(u64::from(len) << 32) | u64::from(ptr)
}

/// Unpacks an `u64` into the pointer and length.
///
/// Runtime API functions return a 64-bit value which encodes a pointer in the least-significant
/// 32-bits and a length in the most-significant 32 bits. This interprets the returned value as a pointer,
/// length tuple.
pub fn unpack_ptr_and_len(val: u64) -> (u32, u32) {
	// The static assertions from above are changed into a runtime check.
	#[cfg(all(not(feature = "std"), feature = "disable_target_static_assertions"))]
	assert_eq!(4, sp_std::mem::size_of::<usize>());

	let ptr = (val & (!0u32 as u64)) as u32;
	let len = (val >> 32) as u32;

	(ptr, len)
}

#[cfg(test)]
mod tests {
	use super::{pack_ptr_and_len, unpack_ptr_and_len};

	#[test]
	fn ptr_len_packing_unpacking() {
		const PTR: u32 = 0x1337;
		const LEN: u32 = 0x7f000000;

		let packed = pack_ptr_and_len(PTR, LEN);
		let (ptr, len) = unpack_ptr_and_len(packed);

		assert_eq!(PTR, ptr);
		assert_eq!(LEN, len);
	}
}
