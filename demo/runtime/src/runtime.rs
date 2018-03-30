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

use runtime_io::BlakeTwo256;
use demo_primitives::{AccountId, Balance, BlockNumber, Hash, Index, SessionKey, Signature};
use {consensus, council, democracy, executive, session, staking, system, timestamp};
use runtime_primitives::{self as primitives, Identity, HasPublicAux};
pub use runtime_primitives::BuildExternalities;

// TODO: refactor so that each module gets to be able to attempt to extract a PrivCall into
// Some(its own PrivCall) or None.
impl democracy::IsCancelReferendum for PrivCall {
	fn is_cancel_referendum(&self) -> Option<democracy::ReferendumIndex> {
		if let &PrivCall::Democracy(democracy::PrivCall::cancel_referendum(ref ref_index)) = self {
			Some(*ref_index)
		} else {
			None
		}
	}
}

pub struct Concrete;

impl HasPublicAux for Concrete {
	type PublicAux = AccountId;
}

impl timestamp::Trait for Concrete {
	type Value = u64;
}
pub type Timestamp = timestamp::Module<Concrete>;

impl consensus::Trait for Concrete {
	type SessionKey = SessionKey;
}
pub type Consensus = consensus::Module<Concrete>;

impl system::Trait for Concrete {
	type Index = Index;
	type BlockNumber = BlockNumber;
	type Hash = Hash;
	type Hashing = BlakeTwo256;
	type Digest = primitives::generic::Digest<Vec<u8>>;
	type AccountId = AccountId;
	type Header = primitives::generic::Header<BlockNumber, Hash, Vec<u8>>;
}
pub type System = system::Module<Concrete>;

impl session::Trait for Concrete {
	type PublicAux = <Self as HasPublicAux>::PublicAux;
	type ConvertAccountIdToSessionKey = Identity;
}
pub type Session = session::Module<Concrete>;

impl staking::Trait for Concrete {
	type Balance = Balance;
	type DetermineContractAddress = BlakeTwo256;
}
pub type Staking = staking::Module<Concrete>;

impl democracy::Trait for Concrete {
	type Proposal = PrivCall;
}
pub type Democracy = democracy::Module<Concrete>;

impl council::Trait for Concrete {}
pub type Council = council::Module<Concrete>;
pub type CouncilVoting = council::voting::Module<Concrete>;

impl_outer_dispatch! {
	pub enum Call where aux: <Concrete as HasPublicAux>::PublicAux {
		Session = 1,
		Staking = 2,
		Timestamp = 3,
		Democracy = 5,
		Council = 6,
		CouncilVoting = 7,
	}

	pub enum PrivCall {
		Consensus = 0,
		Session = 1,
		Staking = 2,
		Democracy = 5,
		Council = 6,
		CouncilVoting = 7,
	}
}

pub type Header = primitives::generic::Header<
	BlockNumber, Hash, Vec<u8>,
>;

pub type Block = primitives::generic::Block<
	BlockNumber, Hash, Vec<u8>, AccountId, Index, Call, Signature
>;

pub type UncheckedExtrinsic = primitives::generic::UncheckedExtrinsic<
	AccountId, Index, Call, Signature
>;

pub type Extrinsic = primitives::generic::Extrinsic<
	AccountId, Index, Call
>;

pub type Executive = executive::Executive<
	Concrete, Block, Staking,
	(((((), Council), Democracy), Staking), Session),
>;

impl_outer_config! {
	pub struct GenesisConfig for Concrete {
		ConsensusConfig => consensus,
		SystemConfig => system,
		SessionConfig => session,
		StakingConfig => staking,
		DemocracyConfig => democracy,
		CouncilConfig => council,
	}
}
