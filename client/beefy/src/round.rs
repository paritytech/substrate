// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

use std::{collections::BTreeMap, hash::Hash};

use log::{debug, trace};

use beefy_primitives::{
	crypto::{Public, Signature},
	ValidatorSet, ValidatorSetId,
};
use sp_arithmetic::traits::AtLeast32BitUnsigned;
use sp_runtime::traits::MaybeDisplay;

#[derive(Default)]
struct RoundTracker {
	votes: Vec<(Public, Signature)>,
}

impl RoundTracker {
	fn add_vote(&mut self, vote: (Public, Signature)) -> bool {
		// this needs to handle equivocations in the future
		if self.votes.contains(&vote) {
			return false
		}

		self.votes.push(vote);
		true
	}

	fn is_done(&self, threshold: usize) -> bool {
		self.votes.len() >= threshold
	}
}

fn threshold(authorities: usize) -> usize {
	let faulty = authorities.saturating_sub(1) / 3;
	authorities - faulty
}

pub(crate) struct Rounds<Hash, Number> {
	rounds: BTreeMap<(Hash, Number), RoundTracker>,
	validator_set: ValidatorSet<Public>,
}

impl<H, N> Rounds<H, N>
where
	H: Ord + Hash,
	N: Ord + AtLeast32BitUnsigned + MaybeDisplay,
{
	pub(crate) fn new(validator_set: ValidatorSet<Public>) -> Self {
		Rounds { rounds: BTreeMap::new(), validator_set }
	}
}

impl<H, N> Rounds<H, N>
where
	H: Ord + Hash,
	N: Ord + AtLeast32BitUnsigned + MaybeDisplay,
{
	pub(crate) fn validator_set_id(&self) -> ValidatorSetId {
		self.validator_set.id
	}

	pub(crate) fn validators(&self) -> Vec<Public> {
		self.validator_set.validators.clone()
	}

	pub(crate) fn add_vote(&mut self, round: (H, N), vote: (Public, Signature)) -> bool {
		if self.validator_set.validators.iter().any(|id| vote.0 == *id) {
			self.rounds.entry(round).or_default().add_vote(vote)
		} else {
			false
		}
	}

	pub(crate) fn is_done(&self, round: &(H, N)) -> bool {
		let done = self
			.rounds
			.get(round)
			.map(|tracker| tracker.is_done(threshold(self.validator_set.validators.len())))
			.unwrap_or(false);

		debug!(target: "beefy", "🥩 Round #{} done: {}", round.1, done);

		done
	}

	pub(crate) fn drop(&mut self, round: &(H, N)) -> Option<Vec<Option<Signature>>> {
		trace!(target: "beefy", "🥩 About to drop round #{}", round.1);

		let signatures = self.rounds.remove(round)?.votes;

		Some(
			self.validator_set
				.validators
				.iter()
				.map(|authority_id| {
					signatures.iter().find_map(|(id, sig)| {
						if id == authority_id {
							Some(sig.clone())
						} else {
							None
						}
					})
				})
				.collect(),
		)
	}
}
