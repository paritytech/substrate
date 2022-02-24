use codec::{Decode, Encode, MaxEncodedLen};
use core::ops::{Add, Mul, Sub};
use sp_runtime::{
	traits::{CheckedAdd, One, Zero},
	RuntimeDebug,
};

use super::*;

#[derive(
	Encode,
	Decode,
	MaxEncodedLen,
	TypeInfo,
	Eq,
	PartialEq,
	Copy,
	Clone,
	PartialOrd,
	RuntimeDebug,
	Default,
)]
pub struct WeightV2 {
	pub time: TimeWeight,
	pub bandwidth: StorageWeight,
}

impl WeightV2 {
	pub const MAX: Self = Self { time: TimeWeight::MAX, bandwidth: StorageWeight::MAX };

	pub fn min(&self, other: Self) -> Self {
		Self { time: self.time.min(other.time), bandwidth: self.bandwidth.min(other.bandwidth) }
	}
}

impl From<(TimeWeight, StorageWeight)> for WeightV2 {
	fn from(a: (TimeWeight, StorageWeight)) -> Self {
		Self { time: a.0, bandwidth: a.1 }
	}
}

impl Zero for WeightV2 {
	fn zero() -> Self {
		Self { time: 0, bandwidth: 0 }
	}

	fn is_zero(&self) -> bool {
		self.time == 0 && self.bandwidth == 0
	}
}

impl One for WeightV2 {
	fn one() -> Self {
		Self { time: 1, bandwidth: 1 }
	}
}

impl Add for WeightV2 {
	type Output = Self;
	fn add(self, rhs: Self) -> Self {
		Self { time: self.time + rhs.time, bandwidth: self.bandwidth + rhs.bandwidth }
	}
}

impl Sub for WeightV2 {
	type Output = Self;
	fn sub(self, rhs: Self) -> Self {
		Self { time: self.time - rhs.time, bandwidth: self.bandwidth - rhs.bandwidth }
	}
}

impl From<TimeWeight> for WeightV2 {
	fn from(t: TimeWeight) -> Self {
		Self { time: t, bandwidth: 0 }
	}
}

impl Mul for WeightV2 {
	type Output = Self;
	fn mul(self, b: Self) -> Self {
		Self { time: b.time * self.time, bandwidth: b.bandwidth * self.bandwidth }
	}
}

impl Mul<Perbill> for WeightV2 {
	type Output = Self;
	fn mul(self, b: Perbill) -> Self {
		Self { time: b * self.time, bandwidth: b * self.bandwidth }
	}
}

impl Mul<WeightV2> for Perbill {
	type Output = WeightV2;
	fn mul(self, b: WeightV2) -> WeightV2 {
		WeightV2 { time: self * b.time, bandwidth: self * b.bandwidth }
	}
}

impl Saturating for WeightV2 {
	fn saturating_add(self, rhs: Self) -> Self {
		Self {
			time: self.time.saturating_add(rhs.time),
			bandwidth: self.bandwidth.saturating_add(rhs.bandwidth),
		}
	}

	fn saturating_sub(self, rhs: Self) -> Self {
		Self {
			time: self.time.saturating_sub(rhs.time),
			bandwidth: self.bandwidth.saturating_sub(rhs.bandwidth),
		}
	}

	fn saturating_mul(self, rhs: Self) -> Self {
		Self {
			time: self.time.saturating_mul(rhs.time),
			bandwidth: self.bandwidth.saturating_mul(rhs.bandwidth),
		}
	}

	fn saturating_pow(self, exp: usize) -> Self {
		Self {
			time: self.time.saturating_pow(exp as u32),
			bandwidth: self.bandwidth.saturating_pow(exp as u32),
		}
	}
}

impl CheckedAdd for WeightV2 {
	fn checked_add(&self, rhs: &Self) -> Option<Self> {
		let time = self.time.checked_add(rhs.time)?;
		let bandwidth = self.bandwidth.checked_add(rhs.bandwidth)?;
		Some(Self { time, bandwidth })
	}
}
