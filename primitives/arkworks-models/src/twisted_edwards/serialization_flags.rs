use ark_ff::Field;
use ark_serialize::Flags;

/// Flags to be encoded into the serialization.
/// The default flags (empty) should not change the binary representation.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TEFlags {
	XIsPositive = 0,
	XIsNegative = 1,
}

impl TEFlags {
	#[inline]
	pub fn from_x_coordinate(x: impl Field) -> Self {
		if x <= -x {
			TEFlags::XIsPositive
		} else {
			TEFlags::XIsNegative
		}
	}

	#[inline]
	pub fn is_negative(&self) -> bool {
		matches!(*self, TEFlags::XIsNegative)
	}
}

impl Default for TEFlags {
	#[inline]
	fn default() -> Self {
		// XIsPositive doesn't change the serialization
		TEFlags::XIsPositive
	}
}

impl Flags for TEFlags {
	const BIT_SIZE: usize = 1;

	#[inline]
	fn u8_bitmask(&self) -> u8 {
		let mut mask = 0;
		if let Self::XIsNegative = self {
			mask |= 1 << 7;
		}
		mask
	}

	#[inline]
	fn from_u8(value: u8) -> Option<Self> {
		let x_sign = (value >> 7) & 1 == 1;
		if x_sign {
			Some(Self::XIsNegative)
		} else {
			Some(Self::XIsPositive)
		}
	}
}
