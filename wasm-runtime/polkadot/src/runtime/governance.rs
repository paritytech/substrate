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

//! Governance system: Handles administration and dispatch of sensitive operations including
//! setting new code, minting new tokens and changing parameters.

use runtime_support::Vec;
use keyedvec::KeyedVec;
use storable::{Storable, StorageVec, kill};
use primitives::{AccountID, Hash, BlockNumber};
use proposal::Proposal;
use runtime::{staking, system, session};

// TRANSACTION API

pub fn propose(transactor: &AccountID, proposal: &Proposal) {
	if Proposal::lookup(b"gov:pro").is_some() {
		panic!("there may only be one proposal per era.");
	}
	proposal.store(b"gov:pro");
	approve(transactor, staking::current_era());
}

pub fn approve(transactor: &AccountID, era_index: BlockNumber) {
	if era_index != staking::current_era() {
		panic!("approval vote applied on non-current era.")
	}
	if Proposal::lookup(b"gov:pro").is_none() {
		panic!("there must be a proposal in order to approve.");
	}
	let key = transactor.to_keyed_vec(b"gov:app:");
	if bool::lookup(&key).is_some() {
		panic!("transactor may not approve a proposal twice in one era.");
	}
	true.store(&key);
	(approval_count() + 1).store(b"gov:app");
}

// INSPECTION API

pub fn approval_count() -> u32 {
	Storable::lookup_default(b"gov:app")
}

pub fn approval_ppm_required() -> u32 {
	Storable::lookup(b"gov:apr").unwrap_or(1000)
}

pub fn approvals_required() -> u32 {
	approval_ppm_required() * staking::validator_count() as u32 / 1000
}

// PUBLIC API

/// Current era is ending; we should finish up any proposals.
pub fn end_of_an_era() {
	// TODO: tally up votes for the current proposal, if any. enact if there are sufficient
	// approvals.
	if let Some(proposal) = Proposal::lookup(b"gov:pro") {
		let enact = approval_count() >= approvals_required();

		// clear proposal
		reset_proposal();

		if enact {
			proposal.enact();
		}
	}
}

// PRIVATE API

fn reset_proposal() {
	session::validators().into_iter().for_each(|v| {
		kill(&v.to_keyed_vec(b"gov:app:"));
	});
	kill(b"gov:pro");
	kill(b"gov:app");
}

#[cfg(test)]
mod tests {
	// TODO
}
