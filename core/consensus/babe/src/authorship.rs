// Copyright 2019 Parity Technologies (UK) Ltd.
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

use merlin::Transcript;
use babe_primitives::{AuthorityId, BabeAuthorityWeight, BABE_ENGINE_ID, BABE_VRF_PREFIX};
use primitives::{U256, blake2_256};
use codec::Encode;
use schnorrkel::vrf::VRFInOut;

/// Calculates the primary selection threshold for a given authority, taking
/// into account `c` (`1 - c` represents the probability of a slot being empty).
pub(super) fn calculate_primary_threshold(
	c: (u64, u64),
	authorities: &[(AuthorityId, BabeAuthorityWeight)],
	authority_index: usize,
) -> u128 {
	use num_bigint::BigUint;
	use num_rational::BigRational;
	use num_traits::{cast::ToPrimitive, identities::One};

	let c = c.0 as f64 / c.1 as f64;

	let theta =
		authorities[authority_index].1 as f64 /
		authorities.iter().map(|(_, weight)| weight).sum::<u64>() as f64;

	let calc = || {
		let p = BigRational::from_float(1f64 - (1f64 - c).powf(theta))?;
		let numer = p.numer().to_biguint()?;
		let denom = p.denom().to_biguint()?;
		((BigUint::one() << 128) * numer / denom).to_u128()
	};

	calc().unwrap_or(u128::max_value())
}

/// Returns true if the given VRF output is lower than the given threshold,
/// false otherwise.
pub(super) fn check_primary_threshold(inout: &VRFInOut, threshold: u128) -> bool {
	u128::from_le_bytes(inout.make_bytes::<[u8; 16]>(BABE_VRF_PREFIX)) < threshold
}

/// Get the expected secondary author for the given slot and with given
/// authorities. This should always assign the slot to some authority unless the
/// authorities list is empty.
pub(super) fn secondary_slot_author(
	slot_number: u64,
	authorities: &[(AuthorityId, BabeAuthorityWeight)],
	randomness: [u8; 32],
) -> Option<&AuthorityId> {
	if authorities.is_empty() {
		return None;
	}

	let rand = U256::from((randomness, slot_number).using_encoded(blake2_256));

	let authorities_len = U256::from(authorities.len());
	let idx = rand % authorities_len;

	let expected_author = authorities.get(idx.as_u32() as usize)
		.expect("authorities not empty; index constrained to list length; \
				this is a valid index; qed");

	Some(&expected_author.0)
}

#[allow(deprecated)]
pub(super) fn make_transcript(
	randomness: &[u8],
	slot_number: u64,
	epoch: u64,
) -> Transcript {
	let mut transcript = Transcript::new(&BABE_ENGINE_ID);
	transcript.commit_bytes(b"slot number", &slot_number.to_le_bytes());
	transcript.commit_bytes(b"current epoch", &epoch.to_le_bytes());
	transcript.commit_bytes(b"chain randomness", randomness);
	transcript
}
