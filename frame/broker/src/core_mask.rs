// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use codec::{Decode, Encode, MaxEncodedLen};
use core::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not};
use scale_info::TypeInfo;
use sp_core::RuntimeDebug;

/// The number of bits in the `CoreMask`.
pub const CORE_MASK_BITS: usize = 80;

// TODO: Use BitArr instead; for this, we'll need to ensure Codec is impl'ed for `BitArr`.
#[derive(
	Encode, Decode, Default, Copy, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen,
)]
pub struct CoreMask([u8; 10]);
impl CoreMask {
	pub fn void() -> Self {
		Self([0u8; 10])
	}
	pub fn complete() -> Self {
		Self([255u8; 10])
	}
	pub fn is_void(&self) -> bool {
		&self.0 == &[0u8; 10]
	}
	pub fn is_complete(&self) -> bool {
		&self.0 == &[255u8; 10]
	}
	pub fn set(&mut self, i: u32) -> Self {
		if i < 80 {
			self.0[(i / 8) as usize] |= 128 >> (i % 8);
		}
		*self
	}
	pub fn clear(&mut self, i: u32) -> Self {
		if i < 80 {
			self.0[(i / 8) as usize] &= !(128 >> (i % 8));
		}
		*self
	}
	pub fn count_zeros(&self) -> u32 {
		self.0.iter().map(|i| i.count_zeros()).sum()
	}
	pub fn count_ones(&self) -> u32 {
		self.0.iter().map(|i| i.count_ones()).sum()
	}
	pub fn from_chunk(from: u32, to: u32) -> Self {
		let mut v = [0u8; 10];
		for i in (from.min(80) as usize)..(to.min(80) as usize) {
			v[i / 8] |= 128 >> (i % 8);
		}
		Self(v)
	}
}
impl From<u128> for CoreMask {
	fn from(x: u128) -> Self {
		let mut v = [0u8; 10];
		v.iter_mut().rev().fold(x, |a, i| {
			*i = a as u8;
			a >> 8
		});
		Self(v)
	}
}
impl From<CoreMask> for u128 {
	fn from(x: CoreMask) -> Self {
		x.0.into_iter().fold(0u128, |a, i| a << 8 | i as u128)
	}
}
impl BitAnd<Self> for CoreMask {
	type Output = Self;
	fn bitand(mut self, rhs: Self) -> Self {
		self.bitand_assign(rhs);
		self
	}
}
impl BitAndAssign<Self> for CoreMask {
	fn bitand_assign(&mut self, rhs: Self) {
		for i in 0..10 {
			self.0[i].bitand_assign(rhs.0[i]);
		}
	}
}
impl BitOr<Self> for CoreMask {
	type Output = Self;
	fn bitor(mut self, rhs: Self) -> Self {
		self.bitor_assign(rhs);
		self
	}
}
impl BitOrAssign<Self> for CoreMask {
	fn bitor_assign(&mut self, rhs: Self) {
		for i in 0..10 {
			self.0[i].bitor_assign(rhs.0[i]);
		}
	}
}
impl BitXor<Self> for CoreMask {
	type Output = Self;
	fn bitxor(mut self, rhs: Self) -> Self {
		self.bitxor_assign(rhs);
		self
	}
}
impl BitXorAssign<Self> for CoreMask {
	fn bitxor_assign(&mut self, rhs: Self) {
		for i in 0..10 {
			self.0[i].bitxor_assign(rhs.0[i]);
		}
	}
}
impl Not for CoreMask {
	type Output = Self;
	fn not(self) -> Self {
		let mut result = [0u8; 10];
		for i in 0..10 {
			result[i] = self.0[i].not();
		}
		Self(result)
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn complete_works() {
		assert_eq!(CoreMask::complete(), CoreMask([0xff; 10]));
		assert!(CoreMask([0xff; 10]).is_complete());
		for i in 0..80 {
			assert!(!CoreMask([0xff; 10]).clear(i).is_complete());
		}
	}

	#[test]
	fn void_works() {
		assert_eq!(CoreMask::void(), CoreMask([0; 10]));
		assert!(CoreMask([0; 10]).is_void());
		for i in 0..80 {
			assert!(!(CoreMask([0; 10]).set(i).is_void()));
		}
	}

	#[test]
	fn from_works() {
		assert!(CoreMask::from(0xfffff_fffff_fffff_fffff).is_complete());
		assert_eq!(
			CoreMask::from(0x12345_67890_abcde_f0123),
			CoreMask([0x12, 0x34, 0x56, 0x78, 0x90, 0xab, 0xcd, 0xef, 0x01, 0x23]),
		);
	}

	#[test]
	fn into_works() {
		assert_eq!(u128::from(CoreMask::complete()), 0xfffff_fffff_fffff_fffff);
		assert_eq!(
			0x12345_67890_abcde_f0123u128,
			CoreMask([0x12, 0x34, 0x56, 0x78, 0x90, 0xab, 0xcd, 0xef, 0x01, 0x23]).into(),
		);
	}

	#[test]
	fn chunk_works() {
		assert_eq!(CoreMask::from_chunk(40, 60), CoreMask::from(0x00000_00000_fffff_00000),);
	}

	#[test]
	fn bit_or_works() {
		assert_eq!(
			CoreMask::from(0x02040_a0c0e_d0a0b_0ffff) | CoreMask::from(0x10305_0b0d0_0e0d0_e0000),
			CoreMask::from(0x12345_abcde_deadb_effff),
		);
	}

	#[test]
	fn bit_or_assign_works() {
		let mut a = CoreMask::from(0x02040_a0c0e_d0a0b_0ffff);
		a |= CoreMask::from(0x10305_0b0d0_0e0d0_e0000);
		assert_eq!(a, CoreMask::from(0x12345_abcde_deadb_effff));
	}

	#[test]
	fn bit_and_works() {
		assert_eq!(
			CoreMask::from(0x00000_abcde_deadb_efff0) & CoreMask::from(0x02040_00000_d0a0b_0ff0f),
			CoreMask::from(0x00000_00000_d0a0b_0ff00),
		);
	}

	#[test]
	fn bit_and_assign_works() {
		let mut a = CoreMask::from(0x00000_abcde_deadb_efff0);
		a &= CoreMask::from(0x02040_00000_d0a0b_0ff0f);
		assert_eq!(a, CoreMask::from(0x00000_00000_d0a0b_0ff00));
	}

	#[test]
	fn bit_xor_works() {
		assert_eq!(
			CoreMask::from(0x10010_10010_10010_10010) ^ CoreMask::from(0x01110_01110_01110_01110),
			CoreMask::from(0x11100_11100_11100_11100),
		);
	}

	#[test]
	fn bit_xor_assign_works() {
		let mut a = CoreMask::from(0x10010_10010_10010_10010);
		a ^= CoreMask::from(0x01110_01110_01110_01110);
		assert_eq!(a, CoreMask::from(0x11100_11100_11100_11100));
	}
}
