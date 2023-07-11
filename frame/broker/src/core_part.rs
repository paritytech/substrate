use codec::{Encode, Decode, MaxEncodedLen};
use scale_info::TypeInfo;
use sp_core::RuntimeDebug;
use core::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not};

// TODO: Use BitArr instead; for this, we'll need to ensure Codec is impl'ed for `BitArr`.
#[derive(Encode, Decode, Default, Copy, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub struct CorePart([u8; 10]);
impl CorePart {
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
impl From<u128> for CorePart {
	fn from(x: u128) -> Self {
		let mut v = [0u8; 10];
		v.iter_mut().rev().fold(x, |a, i| { *i = a as u8; a >> 8 });
		Self(v)
	}
}
impl From<CorePart> for u128 {
	fn from(x: CorePart) -> Self {
		x.0.into_iter().fold(0u128, |a, i| a << 8 | i as u128)
	}
}
impl BitAnd<Self> for CorePart {
	type Output = Self;
	fn bitand(self, rhs: Self) -> Self {
		let mut result = [0u8; 10];
		for i in 0..10 {
			result[i] = self.0[i].bitand(rhs.0[i]);
		}
		Self(result)
	}
}
impl BitAndAssign<Self> for CorePart {
	fn bitand_assign(&mut self, rhs: Self) {
		for i in 0..10 {
			self.0[i].bitand_assign(rhs.0[i]);
		}
	}
}
impl BitOr<Self> for CorePart {
	type Output = Self;
	fn bitor(self, rhs: Self) -> Self {
		let mut result = [0u8; 10];
		for i in 0..10 {
			result[i] = self.0[i].bitor(rhs.0[i]);
		}
		Self(result)
	}
}
impl BitOrAssign<Self> for CorePart {
	fn bitor_assign(&mut self, rhs: Self) {
		for i in 0..10 {
			self.0[i].bitor_assign(rhs.0[i]);
		}
	}
}
impl BitXor<Self> for CorePart {
	type Output = Self;
	fn bitxor(self, rhs: Self) -> Self {
		let mut result = [0u8; 10];
		for i in 0..10 {
			result[i] = self.0[i].bitxor(rhs.0[i]);
		}
		Self(result)
	}
}
impl BitXorAssign<Self> for CorePart {
	fn bitxor_assign(&mut self, rhs: Self) {
		for i in 0..10 {
			self.0[i].bitxor_assign(rhs.0[i]);
		}
	}
}
impl Not for CorePart {
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
		assert_eq!(CorePart::complete(), CorePart([0xff; 10]));
		assert!(CorePart([0xff; 10]).is_complete());
		for i in 0..80 {
			assert!(!CorePart([0xff; 10]).clear(i).is_complete());
		}
	}

	#[test]
	fn void_works() {
		assert_eq!(CorePart::void(), CorePart([0; 10]));
		assert!(CorePart([0; 10]).is_void());
		for i in 0..80 {
			assert!(!(CorePart([0; 10]).set(i).is_void()));
		}
	}

	#[test]
	fn from_works() {
		assert!(CorePart::from(0xfffff_fffff_fffff_fffff).is_complete());
		assert_eq!(
			CorePart::from(0x12345_67890_abcde_f0123),
			CorePart([0x12, 0x34, 0x56, 0x78, 0x90, 0xab, 0xcd, 0xef, 0x01, 0x23]),
		);
	}

	#[test]
	fn into_works() {
		assert_eq!(u128::from(CorePart::complete()), 0xfffff_fffff_fffff_fffff);
		assert_eq!(
			0x12345_67890_abcde_f0123u128,
			CorePart([0x12, 0x34, 0x56, 0x78, 0x90, 0xab, 0xcd, 0xef, 0x01, 0x23]).into(),
		);
	}

	#[test]
	fn chunk_works() {
		assert_eq!(
			CorePart::from_chunk(40, 60),
			CorePart::from(0x00000_00000_fffff_00000),
		);
	}
}