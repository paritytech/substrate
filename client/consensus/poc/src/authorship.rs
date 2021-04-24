// TODO: remove this

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// Copyright (C) 2021 Subpace Labs, Inc.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! PoC farmer selection and slot claiming.

use sp_consensus_poc::POC_VRF_PREFIX;
use schnorrkel::{
	vrf::VRFInOut,
};

/// Calculates the threshold, taking
/// into account `c` (`1 - c` represents the probability of a slot being empty).
pub(super) fn calculate_threshold(c: (u64, u64)) -> u128 {
	use num_bigint::BigUint;
	use num_rational::BigRational;
	use num_traits::{cast::ToPrimitive, identities::One};

	let c = c.0 as f64 / c.1 as f64;

	// TODO: Adjust PoS to PoC
	let theta = 1.0;
		// authorities[authority_index].1 as f64 /
		// authorities.iter().map(|(_, weight)| weight).sum::<u64>() as f64;

	assert!(theta > 0.0, "authority with weight 0.");

	// NOTE: in the equation `p = 1 - (1 - c)^theta` the value of `p` is always
	// capped by `c`. For all practical purposes `c` should always be set to a
	// value < 0.5, as such in the computations below we should never be near
	// edge cases like `0.999999`.

	let p = BigRational::from_float(1f64 - (1f64 - c).powf(theta)).expect(
		"returns None when the given value is not finite; \
		 c is a configuration parameter defined in (0, 1]; \
		 theta must be > 0 if the given authority's weight is > 0; \
		 theta represents the validator's relative weight defined in (0, 1]; \
		 powf will always return values in (0, 1] given both the \
		 base and exponent are in that domain; \
		 qed.",
	);

	let numer = p.numer().to_biguint().expect(
		"returns None when the given value is negative; \
		 p is defined as `1 - n` where n is defined in (0, 1]; \
		 p must be a value in [0, 1); \
		 qed."
	);

	let denom = p.denom().to_biguint().expect(
		"returns None when the given value is negative; \
		 p is defined as `1 - n` where n is defined in (0, 1]; \
		 p must be a value in [0, 1); \
		 qed."
	);

	((BigUint::one() << 128) * numer / denom).to_u128().expect(
		"returns None if the underlying value cannot be represented with 128 bits; \
		 we start with 2^128 which is one more than can be represented with 128 bits; \
		 we multiple by p which is defined in [0, 1); \
		 the result must be lower than 2^128 by at least one and thus representable with 128 bits; \
		 qed.",
	)
}

/// Returns true if the given VRF output is lower than the given threshold,
/// false otherwise.
pub(super) fn check_threshold(inout: &VRFInOut, threshold: u128) -> bool {
	u128::from_le_bytes(inout.make_bytes::<[u8; 16]>(POC_VRF_PREFIX)) < threshold
}
