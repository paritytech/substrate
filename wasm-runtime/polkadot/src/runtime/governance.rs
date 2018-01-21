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
//!
//! For now this is limited to a simple qualified majority vote (whose parameter is retrieved from
//! storage) between validators. A single vote may be proposed per era, and at most one approval
//! vote may be cast by each validator. The tally is maintained through a simple tag in storage for
//! each validator that has approved.
//!
//! At the end of the era, all validators approvals are tallied and if there are sufficient to pass
//! the proposal then it is enacted. All items in storage concerning the proposal are reset.

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

pub fn approve(validator: &AccountID, era_index: BlockNumber) {
	if era_index != staking::current_era() {
		panic!("approval vote applied on non-current era.")
	}
	if Proposal::lookup(b"gov:pro").is_none() {
		panic!("there must be a proposal in order to approve.");
	}
	if session::validators().into_iter().position(|v| &v == validator).is_none() {
		panic!("transactor must be a validator to approve.");
	}
	let key = validator.to_keyed_vec(b"gov:app:");
	if bool::lookup(&key).is_some() {
		panic!("transactor may not approve a proposal twice in one era.");
	}
	true.store(&key);
}

pub fn set_approval_ppm_required(ppm: u32) {
	ppm.store(b"gov:apr");
}

// INSPECTION API

pub fn approval_ppm_required() -> u32 {
	Storable::lookup(b"gov:apr").unwrap_or(1000)
}

pub fn approvals_required() -> u32 {
	approval_ppm_required() * staking::validator_count() as u32 / 1000
}

// PUBLIC API

/// Current era is ending; we should finish up any proposals.
pub fn end_of_an_era() {
	// tally up votes for the current proposal, if any. enact if there are sufficient approvals.
	if let Some(proposal) = Proposal::lookup(b"gov:pro") {
		kill(b"gov:pro");
		let approved: u32 = session::validators().into_iter()
			.map(|v| bool::take(&v.to_keyed_vec(b"gov:app:")).map(|_| 1).unwrap_or(0))
			.sum();
		if approved >= approvals_required() {
			proposal.enact();
		}
	}
}

// PRIVATE API

#[cfg(test)]
mod tests {
	// TODO
}
