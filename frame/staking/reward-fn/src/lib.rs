// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

#![cfg_attr(not(feature = "std"), no_std)]

//! Useful function for inflation for nominated proof of stake.

use sp_arithmetic::{Perquintill, PerThing, biguint::BigUint, traits::{Zero, SaturatedConversion}};
use core::convert::TryFrom;

/// Compute yearly inflation using function
///
/// ```ignore
/// I(x) = for x between 0 and x_ideal: x / x_ideal,
/// for x between x_ideal and 1: 2^((x_ideal - x) / d)
/// ```
///
/// where:
/// * x is the stake rate, i.e. fraction of total issued tokens that actively staked behind
///   validators.
/// * d is the falloff or `decay_rate`
/// * x_ideal: the ideal stake rate.
///
/// The result is meant to be scaled with minimum inflation and maximum inflation.
///
/// (as detailed
/// [here](https://research.web3.foundation/en/latest/polkadot/economics/1-token-economics.html#inflation-model-with-parachains))
///
/// Arguments are:
/// * `stake`:
///   The fraction of total issued tokens that actively staked behind
///   validators. Known as `x` in the literature.
///   Must be between 0 and 1.
/// * `ideal_stake`:
///   The fraction of total issued tokens that should be actively staked behind
///   validators. Known as `x_ideal` in the literature.
///   Must be between 0 and 1.
/// * `falloff`:
///   Known as `decay_rate` in the literature. A co-efficient dictating the strength of
///   the global incentivization to get the `ideal_stake`. A higher number results in less typical
///   inflation at the cost of greater volatility for validators.
///   Must be more than 0.01.
pub fn compute_inflation<P: PerThing>(
	stake: P,
	ideal_stake: P,
	falloff: P,
) -> P {
	if stake < ideal_stake {
		// ideal_stake is more than 0 because it is strictly more than stake
		return stake / ideal_stake
	}

	if falloff < P::from_percent(1.into()) {
		log::error!("Invalid inflation computation: falloff less than 1% is not supported");
		return PerThing::zero()
	}

	let accuracy = {
		let mut a = BigUint::from(Into::<u128>::into(P::ACCURACY));
		a.lstrip();
		a
	};

	let mut falloff = BigUint::from(falloff.deconstruct().into());
	falloff.lstrip();

	let ln2 = {
		let ln2 = P::from_rational(LN2.deconstruct().into(), Perquintill::ACCURACY.into());
		BigUint::from(ln2.deconstruct().into())
	};

	// falloff is stripped above.
	let ln2_div_d = div_by_stripped(ln2.mul(&accuracy), &falloff);

	let inpos_param = INPoSParam {
		x_ideal: BigUint::from(ideal_stake.deconstruct().into()),
		x: BigUint::from(stake.deconstruct().into()),
		accuracy,
		ln2_div_d,
	};

	let res = compute_taylor_serie_part(&inpos_param);

	match u128::try_from(res.clone()) {
		Ok(res) if res <= Into::<u128>::into(P::ACCURACY) => {
			P::from_parts(res.saturated_into())
		},
		// If result is beyond bounds there is nothing we can do
		_ => {
			log::error!("Invalid inflation computation: unexpected result {:?}", res);
			P::zero()
		},
	}
}


/// Internal struct holding parameter info alongside other cached value.
///
/// All expressed in part from `accuracy`
struct INPoSParam {
	ln2_div_d: BigUint,
	x_ideal: BigUint,
	x: BigUint,
	/// Must be stripped and have no leading zeros.
	accuracy: BigUint,
}

/// `ln(2)` expressed in as perquintillionth.
const LN2: Perquintill = Perquintill::from_parts(0_693_147_180_559_945_309);

/// Compute `2^((x_ideal - x) / d)` using taylor serie.
///
/// x must be strictly more than x_ideal.
///
/// result is expressed with accuracy `INPoSParam.accuracy`
fn compute_taylor_serie_part(p: &INPoSParam) -> BigUint {
	// The last computed taylor term.
	let mut last_taylor_term = p.accuracy.clone();

	// Whereas taylor sum is positive.
	let mut taylor_sum_positive = true;

	// The sum of all taylor term.
	let mut taylor_sum = last_taylor_term.clone();

	for k in 1..300 {
		last_taylor_term = compute_taylor_term(k, &last_taylor_term, p);

		if last_taylor_term.is_zero() {
			break
		}

		let last_taylor_term_positive = k % 2 == 0;

		if taylor_sum_positive == last_taylor_term_positive {
			taylor_sum = taylor_sum.add(&last_taylor_term);
		} else {
			if taylor_sum >= last_taylor_term {
				taylor_sum = taylor_sum.sub(&last_taylor_term)
					// NOTE: Should never happen as checked above
					.unwrap_or_else(|e| e);
			} else {
				taylor_sum_positive = !taylor_sum_positive;
				taylor_sum = last_taylor_term.clone().sub(&taylor_sum)
					// NOTE: Should never happen as checked above
					.unwrap_or_else(|e| e);
			}
		}
	}

	if !taylor_sum_positive {
		return BigUint::zero()
	}

	taylor_sum.lstrip();
	taylor_sum
}

/// Return the absolute value of k-th taylor term of `2^((x_ideal - x))/d` i.e.
/// `((x - x_ideal) * ln(2) / d)^k / k!`
///
/// x must be strictly more x_ideal.
///
/// We compute the term from the last term using this formula:
///
/// `((x - x_ideal) * ln(2) / d)^k / k! == previous_term * (x - x_ideal) * ln(2) / d / k`
///
/// `previous_taylor_term` and result are expressed with accuracy `INPoSParam.accuracy`
fn compute_taylor_term(k: u32, previous_taylor_term: &BigUint, p: &INPoSParam) -> BigUint {
	let x_minus_x_ideal = p.x.clone().sub(&p.x_ideal)
		// NOTE: Should never happen, as x must be more than x_ideal
		.unwrap_or_else(|_| BigUint::zero());

	let res = previous_taylor_term.clone()
		.mul(&x_minus_x_ideal)
		.mul(&p.ln2_div_d)
		.div_unit(k);

	// p.accuracy is stripped by definition.
	let res = div_by_stripped(res, &p.accuracy);
	let mut res = div_by_stripped(res, &p.accuracy);

	res.lstrip();
	res
}

/// Compute a div b.
///
/// requires `b` to be stripped and have no leading zeros.
fn div_by_stripped(mut a: BigUint, b: &BigUint) -> BigUint {
	a.lstrip();

	if b.len() == 0 {
		log::error!("Computation error: Invalid division");
		return BigUint::zero()
	}

	if b.len() == 1 {
		return a.div_unit(b.checked_get(0).unwrap_or(1))
	}

	if b.len() > a.len() {
		return BigUint::zero()
	}

	if b.len() == a.len() {
		// 100_000^2 is more than 2^32-1, thus `new_a` has more limbs than `b`.
		let mut new_a = a.mul(&BigUint::from(100_000u64.pow(2)));
		new_a.lstrip();

		debug_assert!(new_a.len() > b.len());
		return new_a
			.div(b, false)
			.map(|res| res.0)
			.unwrap_or_else(|| BigUint::zero())
			.div_unit(100_000)
			.div_unit(100_000)
	}

	a.div(b, false)
		.map(|res| res.0)
		.unwrap_or_else(|| BigUint::zero())
}
