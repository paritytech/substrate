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

//! Collation Logic.
//!
//! A collator node lives on a distinct parachain and submits a proposal for
//! a state transition, along with a proof for its validity (what we call a witness).
//!
//! One of the other strengths of Polkadot is its ability to route messages
//! between chains. Each parachain has an "egress" queue of messages for each
//! other parachain, for a total of N^2 queues all together.
//!
//! We will refer to the egress queue of parachain A with destination B as
//! egress[A -> B]
//!
//! On every block, each parachain will be intended to route messages from some
//! subset of all the other parachains. Routing messages from a parachain B to A
//! involves fully draining egress[B -> A]. The proposal for parachain A may
//! additionally post new messages to egress[A -> _].
//!
//! Along with the proposal and witness, the collator passes this list of posts to
//! the validator. The posts contains a mapping of parachain identifiers to
//! a list of two new tree roots.
//!
//! Since a parachain X may either fully drain egress[A -> X] or leave it untouched,
//! the first root is the root of the empty list concatenated with the posts to X,
//! while the second is the root of the queue at the prior relay chain block
//! with the posts to X concatenated. These two alternatives allow the relay
//! chain block to be constructed correctly regardless of whetherh candidates
//! from other parachains are actually included.
//!
//! This crate defines traits which provide context necessary for collation logic
//! to be performed, as the collation logic itself.

extern crate polkadot_primitives as primitives;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
    }
}
