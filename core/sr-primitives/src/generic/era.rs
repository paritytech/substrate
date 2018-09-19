// Copyright 2017 Parity Technologies (UK) Ltd.
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

use codec::{Decode, Encode, Input, Output};

pub type Period = u64;
pub type Phase = u64;

/// An era to describe the longevity of a transaction.
#[derive(PartialEq, Eq, Clone, Copy)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub enum Era {
	/// The transaction is valid forever. The genesis hash must be present in the signed content.
	Immortal,

	/// Period and phase are encoded:
	/// - The period of validity from the block hash found in the signing material.
	/// - The phase in the period that this transaction's lifetime begins (and, importantly,
	/// implies which block hash is included in the signature material). If the `period` is
	/// greater than 1 << 12, then it will be a factor of the times greater than 1<<12 that
	/// `period` is.
	Mortal(Period, Phase),
}

/*
E.g. with period == 4:
0         10        20        30        40
0123456789012345678901234567890123456789012
             |...|
   authored -/   \- expiry
phase = 1
n = Q(current - phase, period) + phase
*/
impl Era {
	/// Create a new era based on a period (which should be a power of two between 4 and 65536 inclusive)
	/// and a block number which on which it should start (or, for long periods, be shortly after the start).
	pub fn new(period: u64, current: u64) -> Self {
		let period = period.checked_next_power_of_two()
			.unwrap_or(1 << 16)
			.max(4)
			.min(1 << 16);
		let phase = current - current / period * period;
		let quantize_factor = (period >> 12).max(1);
		let quantized_phase = (phase / quantize_factor * quantize_factor).min(1 << 12 - 1);

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
			Era::Mortal(period, phase) => (current - phase) / period * period + phase,
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
				let encoded = (period.trailing_zeros() - 1).max(1).min(15) as u16 | ((phase / quantize_factor) >> 4) as u16;
				output.push(&encoded);
			}
		}
	}
}

impl Decode for Era {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		let first = input.read_byte()?;
		if first == 0 {
			Some(Era::Immortal)
		} else {
			let encoded = first as u64 + (input.read_byte()? as u64 >> 8);
			let period = 2 << (encoded % (1 << 4));
			let quantize_factor = (period >> 12).max(1);
			let phase = (encoded >> 4) * quantize_factor;
			if period >= 4 && phase < period {
				Some(Era::Mortal(period, phase))
			} else {
				None
			}
		}
	}
}