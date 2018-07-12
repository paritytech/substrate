// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Utils for block interaction.

use rstd::prelude::*;
use super::{Call, UncheckedExtrinsic, Extrinsic, Staking};
use runtime_primitives::traits::{Checkable, AuxLookup};
use primitives::parachain::CandidateReceipt;
use timestamp::Call as TimestampCall;
use parachains::Call as ParachainsCall;

/// Produces the list of inherent extrinsics.
pub fn inherent_extrinsics(timestamp: ::primitives::Timestamp, parachain_heads: Vec<CandidateReceipt>) -> Vec<UncheckedExtrinsic> {
	vec![
		UncheckedExtrinsic::new(
			Extrinsic {
				signed: Default::default(),
				function: Call::Timestamp(TimestampCall::set(timestamp)),
				index: 0,
			},
			Default::default()
		),
		UncheckedExtrinsic::new(
			Extrinsic {
				signed: Default::default(),
				function: Call::Parachains(ParachainsCall::set_heads(parachain_heads)),
				index: 0,
			},
			Default::default()
		)
	]
}

/// Checks an unchecked extrinsic for validity.
pub fn check_extrinsic(xt: UncheckedExtrinsic) -> bool {
	xt.check_with(Staking::lookup).is_ok()
}
