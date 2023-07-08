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
	pub fn count_zeros(&self) -> u32 {
		self.0.iter().map(|i| i.count_zeros()).sum()
	}
	pub fn count_ones(&self) -> u32 {
		self.0.iter().map(|i| i.count_ones()).sum()
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
