// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! 128-bit shims so that we can make it `serde::Serialize`-able, since Serde is borked for
//! the new 128-bit datatypes.

#[cfg(feature = "std")]
use serde::ser::{Serialize, Serializer, SerializeTuple};
use codec::{Slicable, Input};
use integer_sqrt::IntegerSquareRoot;
use num_traits::{Zero, One, Bounded};
use rstd::ops::{Add, Sub, Mul, Div, Rem, AddAssign, SubAssign, MulAssign, DivAssign, RemAssign};
use traits::As;

/// A 128-bit uint shim.
#[derive(Debug, Eq, PartialEq, PartialOrd, Ord, Clone, Copy, Default)]
pub struct U128(u128);

/// A 128-bit int shim.
#[derive(Debug, Eq, PartialEq, PartialOrd, Ord, Clone, Copy, Default)]
pub struct I128(i128);

macro_rules! impl_as {
	( $f:ident, $i:ty ) => {
		impl_as!($f, $i: u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);
	};
	( $f:ident, $i:ty : $t:ty $(, $rest:ty)* ) => {
		impl As<$t> for $f {
			fn as_(self) -> $t { self.0 as $t }
			fn sa(t: $t) -> Self { $f(t as $i) }
		}
		impl_as!($f, $i : $( $rest ),*);
	};
	( $f:ident, $i:ty : ) => {}
}


macro_rules! impl_for {
	($type:ident, $inner:ty) => {
		impl IntegerSquareRoot for $type {
			fn integer_sqrt(&self) -> Self {
				$type(self.0.integer_sqrt())
			}
			fn integer_sqrt_checked(&self) -> Option<Self> {
				self.0.integer_sqrt_checked().map(|x| $type(x))
			}
		}
		macro_rules! impl_bin_op {
			($op:ident, $f:ident) => {
				impl $op for $type {
					type Output = Self;
					fn $f (self, other: Self) -> Self {
						$type((self.0).$f(other.0))
					}
				}
			}
		}
		macro_rules! impl_assign_op {
			($op:ident, $f:ident) => {
				impl $op for $type {
					fn $f (&mut self, other: Self) {
						(&mut self.0).$f(other.0)
					}
				}
			}
		}
		impl_bin_op!(Add, add);
		impl_bin_op!(Sub, sub);
		impl_bin_op!(Mul, mul);
		impl_bin_op!(Div, div);
		impl_bin_op!(Rem, rem);
		impl_assign_op!(AddAssign, add_assign);
		impl_assign_op!(SubAssign, sub_assign);
		impl_assign_op!(MulAssign, mul_assign);
		impl_assign_op!(DivAssign, div_assign);
		impl_assign_op!(RemAssign, rem_assign);

		impl Zero for $type {
			fn zero() -> Self {
				$type(Zero::zero())
			}
			fn is_zero(&self) -> bool {
				self.0.is_zero()
			}
		}
		impl One for $type {
			fn one() -> Self {
				$type(One::one())
			}
		}

		impl Bounded for $type {
			fn min_value() -> Self {
				$type(Bounded::min_value())
			}
			fn max_value() -> Self {
				$type(Bounded::max_value())
			}
		}

		#[cfg(feature = "std")]
		impl Serialize for $type {
			fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
			where
				S: Serializer,
			{
				let mut seq = serializer.serialize_tuple(2)?;
				seq.serialize_element(&(self.0 as u64))?;
				seq.serialize_element(&((self.0 >> 64) as u64))?;
				seq.end()
			}
		}

		impl Slicable for $type {
			fn decode<I: Input>(input: &mut I) -> Option<Self> {
				Slicable::decode(input).map($type)
			}

			fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
				self.0.using_encoded(f)
			}
		}

		impl From<$inner> for $type {
			fn from(v: $inner) -> Self {
				$type(v)
			}
		}

		impl_as!($type, $inner);
	}
}

impl_for!(U128, u128);
impl_for!(I128, i128);
