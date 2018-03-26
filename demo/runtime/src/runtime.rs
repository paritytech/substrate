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
use runtime_io::{enumerated_trie_root, storage_root};
use {consensus, timestamp, system, session, demo_primitives, runtime_primitives};
use runtime_primitives::{Identity, HasPublicAux};

// TODO: move into runtime support/io.
pub struct BlakeTwo256;
impl runtime_primitives::Hashing for BlakeTwo256 {
	type Output = demo_primitives::Hash;
	fn hash_of<S: Slicable>(s: &S) -> Self::Output {
		Self::Output::from(s.blake2_256())
	}
	fn enumerated_trie_root(items: &Vec<&[u8]>) -> Self::Output {
		enumerated_trie_root(items).into()
	}
	fn storage_root() -> Self::Output {
		storage_root().into()
	}
}

pub struct Concrete;

impl HasPublicAux for Concrete {
	type PublicAux = demo_primitives::AccountId;
}

impl timestamp::Trait for Concrete {
	type Value = u64;
}
pub type Timestamp = timestamp::Module<Concrete>;

impl consensus::Trait for Concrete {
	type SessionKey = demo_primitives::AccountId;
}
pub type Consensus = consensus::Module<Concrete>;

impl system::Trait for Concrete {
	type Index = demo_primitives::TxOrder;
	type BlockNumber = demo_primitives::BlockNumber;
	type Hash = demo_primitives::Hash;
	type Hashing = BlakeTwo256;
	type Digest = demo_primitives::header::Digest;
	type AccountId = demo_primitives::AccountId;
	type Header = demo_primitives::header::Header;
}
pub type System = system::Module<Concrete>;

impl session::Trait for Concrete {
	type PublicAux = <Self as HasPublicAux>::PublicAux;
	type Conversion = Identity;
}
pub type Session = session::Module<Concrete>;

impl_outer_dispatch! {
	pub enum Call where aux: <Concrete as HasPublicAux>::PublicAux {
		Session = 1,
//		Staking = 2,
		Timestamp = 3,
//		Democracy = 5,
//		Council = 6,
//		CouncilVote = 7,
	}

	pub enum PrivCall {
		Consensus = 0,
		Session = 1,
//		Staking = 2,
//		Democracy = 5,
//		Council = 6,
//		CouncilVote = 7,
	}
}
