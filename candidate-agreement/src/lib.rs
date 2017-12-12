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

//! Propagation and agreement of candidates.
//!
//! This is parameterized by 3 numbers:
//! N: the number of validators total
//! P: the number of parachains
//! F: the number of faulty nodes (s.t. 3F + 1 <= N)
//! We also define G as the number of validators per parachain (N/P)
//!
//! Validators are split into groups by parachain, and each validator might come
//! up its own candidate for their parachain. Within groups, validators pass around
//! their candidates and produce statements of validity.
//!
//! Any candidate that receives majority approval by the validators in a group
//! may be subject to inclusion.

extern crate futures;
extern crate polkadot_primitives as primitives;

use primitives::parachain;

pub mod table;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
    }
}
