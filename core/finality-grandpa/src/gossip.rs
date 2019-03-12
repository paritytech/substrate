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

//! Gossip and politeness for GRANDPA communication.

/// An outcome of examining a message.
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Consider {
	/// Accept the message.
	Accept,
	/// Message is too early. Reject.
	RejectPast,
	/// Message is from the future. Reject.
	RejectFuture,
}

/// A view of protocol state.
pub struct View {
	round: u64, // the current round we are at.
	set_id: u64, // the current voter set id.
}

impl View {
	/// A new view of consensus.
	pub fn new(round: u64, set_id: u64) -> Self {
		View { round, set_id }
	}

	/// Get the round number.
	pub fn round(&self) -> u64 { self.round }

	/// Get the set ID.
	pub fn set_id(&self) -> u64 { self.set_id}

	/// Update the round number, implying the same set.
	pub fn update_round(&mut self, new_round: u64) {
		self.round = new_round;
	}

	/// Update the set ID. implies a reset to round 0.
	pub fn update_set(&mut self, set_id: u64) {
		self.set_id = set_id;
		self.round = 0;
	}

	/// Consider a round and set ID combination under a current view.
	pub fn consider(&self, round: u64, set_id: u64) -> Consider {
		// only from current set
		if set_id < self.set_id { return Consider::RejectPast }
		if set_id > self.set_id { return Consider::RejectFuture }

		// only r-1 ... r+1
		if round > self.round.saturating_add(1) { return Consider::RejectFuture }
		if round < self.round.saturating_sub(1) { return Consider::RejectPast }

		Consider::Accept
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn view_accepts_current() {
		let mut view = View::new(100, 1);

		assert_eq!(view.consider(98, 1), Consider::RejectPast);
		assert_eq!(view.consider(1, 0), Consider::RejectPast);
		assert_eq!(view.consider(1000, 0), Consider::RejectPast);

		assert_eq!(view.consider(99, 1), Consider::Accept);
		assert_eq!(view.consider(100, 1), Consider::Accept);
		assert_eq!(view.consider(101, 1), Consider::Accept);

		assert_eq!(view.consider(102, 1), Consider::RejectFuture);
		assert_eq!(view.consider(1, 2), Consider::RejectFuture);
		assert_eq!(view.consider(1000, 2), Consider::RejectFuture);
	}
}
