// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Generic implementation of an unchecked (pre-verification) extrinsic.

#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};

use crate::codec::{Decode, Encode, Input, Output, Error};

/// Era period
pub type Period = u64;

/// Era phase
pub type Phase = u64;

/// An era to describe the longevity of a transaction.
#[derive(PartialEq, Eq, Clone, Copy, sp_core::RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub enum Era {
	/// The transaction is valid forever. The genesis hash must be present in the signed content.
	Immortal,

	/// Period and phase are encoded:
	/// - The period of validity from the block hash found in the signing material.
	/// - The phase in the period that this transaction's lifetime begins (and, importantly,
	/// implies which block hash is included in the signature material). If the `period` is
	/// greater than 1 << 12, then it will be a factor of the times greater than 1<<12 that
	/// `period` is.
	///
	/// When used on `FRAME`-based runtimes, `period` cannot exceed `BlockHashCount` parameter
	/// of `system` module.
	Mortal(Period, Phase),
}

/*
 * E.g. with period == 4:
 * 0         10        20        30        40
 * 0123456789012345678901234567890123456789012
 *              |...|
 *    authored -/   \- expiry
 * phase = 1
 * n = Q(current - phase, period) + phase
 */
impl Era {
	/// Create a new era based on a period (which should be a power of two between 4 and 65536 inclusive)
	/// and a block number on which it should start (or, for long periods, be shortly after the start).
	///
	/// If using `Era` in the context of `FRAME` runtime, make sure that `period`
	/// does not exceed `BlockHashCount` parameter passed to `system` module, since that
	/// prunes old blocks and renders transactions immediately invalid.
	pub fn mortal(period: u64, current: u64) -> Self {
		let period = period.checked_next_power_of_two()
			.unwrap_or(1 << 16)
			.max(4)
			.min(1 << 16);
		let phase = current % period;
		let quantize_factor = (period >> 12).max(1);
		let quantized_phase = phase / quantize_factor * quantize_factor;

		Era::Mortal(period, quantized_phase)
	}

	/// Create an "immortal" transaction.
	pub fn immortal() -> Self {
		Era::Immortal
	}

	/// `true` if this is an immortal transaction.
	pub fn is_immortal(&self) -> bool {
		match self {
			Era::Immortal => true,
			_ => false,
		}
	}

	/// Get the block number of the start of the era whose properties this object
	/// describes that `current` belongs to.
	pub fn birth(self, current: u64) -> u64 {
		match self {
			Era::Immortal => 0,
			Era::Mortal(period, phase) => (current.max(phase) - phase) / period * period + phase,
		}
	}

	/// Get the block number of the first block at which the era has ended.
	pub fn death(self, current: u64) -> u64 {
		match self {
			Era::Immortal => u64::max_value(),
			Era::Mortal(period, _) => self.birth(current) + period,
		}
	}
}

impl Encode for Era {
	fn encode_to<T: Output>(&self, output: &mut T) {
		match self {
			Era::Immortal => output.push_byte(0),
			Era::Mortal(period, phase) => {
				let quantize_factor = (*period as u64 >> 12).max(1);
				let encoded = (period.trailing_zeros() - 1).max(1).min(15) as u16 | ((phase / quantize_factor) << 4) as u16;
				output.push(&encoded);
			}
		}
	}
}

impl codec::EncodeLike for Era {}

impl Decode for Era {
	fn decode<I: Input>(input: &mut I) -> Result<Self, Error> {
		let first = input.read_byte()?;
		if first == 0 {
			Ok(Era::Immortal)
		} else {
			let encoded = first as u64 + ((input.read_byte()? as u64) << 8);
			let period = 2 << (encoded % (1 << 4));
			let quantize_factor = (period >> 12).max(1);
			let phase = (encoded >> 4) * quantize_factor;
			if period >= 4 && phase < period {
				Ok(Era::Mortal(period, phase))
			} else {
				Err("Invalid period and phase".into())
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn immortal_works() {
		let e = Era::immortal();
		assert_eq!(e.birth(0), 0);
		assert_eq!(e.death(0), u64::max_value());
		assert_eq!(e.birth(1), 0);
		assert_eq!(e.death(1), u64::max_value());
		assert_eq!(e.birth(u64::max_value()), 0);
		assert_eq!(e.death(u64::max_value()), u64::max_value());
		assert!(e.is_immortal());

		assert_eq!(e.encode(), vec![0u8]);
		assert_eq!(e, Era::decode(&mut&[0u8][..]).unwrap());
	}

	#[test]
	fn mortal_codec_works() {
		let e = Era::mortal(64, 42);
		assert!(!e.is_immortal());

		let expected = vec![5 + 42 % 16 * 16, 42 / 16];
		assert_eq!(e.encode(), expected);
		assert_eq!(e, Era::decode(&mut&expected[..]).unwrap());
	}

	#[test]
	fn long_period_mortal_codec_works() {
		let e = Era::mortal(32768, 20000);

		let expected = vec![(14 + 2500 % 16 * 16) as u8, (2500 / 16) as u8];
		assert_eq!(e.encode(), expected);
		assert_eq!(e, Era::decode(&mut&expected[..]).unwrap());
	}

	#[test]
	fn era_initialization_works() {
		assert_eq!(Era::mortal(64, 42), Era::Mortal(64, 42));
		assert_eq!(Era::mortal(32768, 20000), Era::Mortal(32768, 20000));
		assert_eq!(Era::mortal(200, 513), Era::Mortal(256, 1));
		assert_eq!(Era::mortal(2, 1), Era::Mortal(4, 1));
		assert_eq!(Era::mortal(4, 5), Era::Mortal(4, 1));
	}

	#[test]
	fn quantized_clamped_era_initialization_works() {
		// clamp 1000000 to 65536, quantize 1000001 % 65536 to the nearest 4
		assert_eq!(Era::mortal(1000000, 1000001), Era::Mortal(65536, 1000001 % 65536 / 4 * 4));
	}

	#[test]
	fn mortal_birth_death_works() {
		let e = Era::mortal(4, 6);
		for i in 6..10 {
			assert_eq!(e.birth(i), 6);
			assert_eq!(e.death(i), 10);
		}

		// wrong because it's outside of the (current...current + period) range
		assert_ne!(e.birth(10), 6);
		assert_ne!(e.birth(5), 6);
	}

	#[test]
	fn current_less_than_phase() {
		// should not panic
		Era::mortal(4, 3).birth(1);
	}
}
