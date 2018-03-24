// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Dispatch system. Just dispatches calls.

use codec::Slicable;
use runtime_support::Hashable;
use {consensus, timestamp, system, demo_primitives, primitives};

// TODO: move into runtime support.
struct BlakeTwo256;
impl system::Hashing for BlakeTwo256 {
	type Output = primitives::H256;
	fn hash_of<S: Slicable>(s: &S) -> Self::Output {
		Self::Output::from(s.blake2_256())
	}
}

type PublicAux = demo_primitives::AccountId;
type PrivAux = ();

#[cfg_attr(feature = "std", derive(Debug))]
struct Concrete;

impl timestamp::Trait for Concrete {
	type Value = u64;
	type PublicAux = PublicAux;
}
type Timestamp = timestamp::Module<Concrete>;

impl consensus::Trait for Concrete {
	type SessionKey = demo_primitives::AccountId;
	type PrivAux = PrivAux;
}
type Consensus = consensus::Module<Concrete>;

impl system::Trait for Concrete {
	type TxOrder = demo_primitives::TxOrder;
	type BlockNumber = demo_primitives::BlockNumber;
	type Hash = demo_primitives::Hash;
	type Hashing = BlakeTwo256;
	type Digest = demo_primitives::block::Digest;
	type AccountId = demo_primitives::AccountId;
}
type System = system::Module<Concrete>;


impl_outer_dispatch! {
	pub enum PubCall where aux: PublicAux {
//		Session = 1,
//		Staking = 2,
		Timestamp = 3,
//		Democracy = 5,
//		Council = 6,
//		CouncilVote = 7,
	}
}

impl_outer_dispatch! {
	pub enum PrivCall where aux: PrivAux {
		Consensus = 0,
//		Session = 1,
//		Staking = 2,
//		Democracy = 5,
//		Council = 6,
//		CouncilVote = 7,
	}
}
