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

//! The Substrate Demo runtime. This can be compiled with ``#[no_std]`, ready for Wasm.

#![cfg_attr(not(feature = "std"), no_std)]

#[macro_use]
extern crate substrate_runtime_io as runtime_io;

#[macro_use]
extern crate substrate_runtime_support;

#[macro_use]
extern crate substrate_runtime_primitives as runtime_primitives;

#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;

#[cfg(feature = "std")]
extern crate serde;

extern crate substrate_codec as codec;

#[macro_use]
extern crate substrate_codec_derive;

extern crate substrate_runtime_std as rstd;
extern crate substrate_runtime_balances as balances;
extern crate substrate_runtime_consensus as consensus;
extern crate substrate_runtime_council as council;
extern crate substrate_runtime_democracy as democracy;
extern crate substrate_runtime_executive as executive;
extern crate substrate_runtime_session as session;
extern crate substrate_runtime_staking as staking;
extern crate substrate_runtime_system as system;
extern crate substrate_runtime_timestamp as timestamp;
#[macro_use]
extern crate substrate_runtime_version as version;
extern crate demo_primitives;

use demo_primitives::{AccountId, AccountIndex, Balance, BlockNumber, Hash, Index, SessionKey, Signature};
use runtime_primitives::generic;
use runtime_primitives::traits::{Convert, BlakeTwo256, DigestItem};
use version::RuntimeVersion;

#[cfg(any(feature = "std", test))]
pub use runtime_primitives::BuildStorage;

// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
/// Runtime runtime type used to parameterize the various modules.
pub struct Runtime;

/// Runtime version.
pub const VERSION: RuntimeVersion = RuntimeVersion {
	spec_name: ver_str!("demo"),
	impl_name: ver_str!("parity-demo"),
	authoring_version: 1,
	spec_version: 1,
	impl_version: 0,
};

/// Version module for this concrete runtime.
pub type Version = version::Module<Runtime>;

impl version::Trait for Runtime {
	const VERSION: RuntimeVersion = VERSION;
}

impl system::Trait for Runtime {
	type PublicAux = Self::AccountId;
	type Index = Index;
	type BlockNumber = BlockNumber;
	type Hash = Hash;
	type Hashing = BlakeTwo256;
	type Digest = generic::Digest<Log>;
	type AccountId = AccountId;
	type Header = generic::Header<BlockNumber, BlakeTwo256, Log>;
	type Event = Event;
}

/// System module for this concrete runtime.
pub type System = system::Module<Runtime>;

impl balances::Trait for Runtime {
	type Balance = Balance;
	type AccountIndex = AccountIndex;
	type OnFreeBalanceZero = Staking;
	type EnsureAccountLiquid = Staking;
	type Event = Event;
}

/// Staking module for this concrete runtime.
pub type Balances = balances::Module<Runtime>;

impl consensus::Trait for Runtime {
	const NOTE_OFFLINE_POSITION: u32 = 1;
	type Log = Log;
	type SessionKey = SessionKey;
	type OnOfflineValidator = Staking;
}

/// Consensus module for this concrete runtime.
pub type Consensus = consensus::Module<Runtime>;

impl timestamp::Trait for Runtime {
	const TIMESTAMP_SET_POSITION: u32 = 0;

	type Moment = u64;
}

/// Timestamp module for this concrete runtime.
pub type Timestamp = timestamp::Module<Runtime>;

/// Session key conversion.
pub struct SessionKeyConversion;
impl Convert<AccountId, SessionKey> for SessionKeyConversion {
	fn convert(a: AccountId) -> SessionKey {
		a.0.into()
	}
}

impl session::Trait for Runtime {
	type ConvertAccountIdToSessionKey = SessionKeyConversion;
	type OnSessionChange = Staking;
	type Event = Event;
}

/// Session module for this concrete runtime.
pub type Session = session::Module<Runtime>;

impl staking::Trait for Runtime {
	type OnRewardMinted = ();
	type Event = Event;
}

/// Staking module for this concrete runtime.
pub type Staking = staking::Module<Runtime>;

impl democracy::Trait for Runtime {
	type Proposal = PrivCall;
}

/// Democracy module for this concrete runtime.
pub type Democracy = democracy::Module<Runtime>;

impl council::Trait for Runtime {}

/// Council module for this concrete runtime.
pub type Council = council::Module<Runtime>;
/// Council voting module for this concrete runtime.
pub type CouncilVoting = council::voting::Module<Runtime>;

impl_outer_event! {
	pub enum Event for Runtime {
		balances, session, staking
	}
}

impl_outer_log! {
	pub enum Log for Runtime {
		consensus
	}
}

impl DigestItem for Log {
	type AuthoritiesChange = consensus::AuthoritiesChange<SessionKey>;

	fn as_authorities_change(&self) -> Option<&Self::AuthoritiesChange> {
		match *self {
			Log::consensus(ref item) => item.as_authorities_change(),
		}
	}
}

impl_outer_dispatch! {
	#[derive(Clone, PartialEq, Eq)]
	#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
	pub enum Call where aux: <Runtime as system::Trait>::PublicAux {
		Consensus,
		Balances,
		Session,
		Staking,
		Timestamp,
		Democracy,
		Council,
		CouncilVoting,
	}

	#[derive(Clone, PartialEq, Eq)]
	#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
	pub enum PrivCall {
		Consensus,
		Balances,
		Session,
		Staking,
		Democracy,
		Council,
		CouncilVoting,
	}
}

/// The address format for describing accounts.
pub type Address = balances::Address<Runtime>;
/// Block header type as expected by this runtime.
pub type Header = generic::Header<BlockNumber, BlakeTwo256, Log>;
/// Block type as expected by this runtime.
pub type Block = generic::Block<Header, UncheckedExtrinsic>;
/// BlockId type as expected by this runtime.
pub type BlockId = generic::BlockId<Block>;
/// Unchecked extrinsic type as expected by this runtime.
pub type UncheckedExtrinsic = generic::UncheckedExtrinsic<Address, Index, Call, Signature>;
/// Extrinsic type as expected by this runtime. This is not the type that is signed.
pub type Extrinsic = generic::Extrinsic<Address, Index, Call>;
/// Extrinsic type that is signed.
pub type BareExtrinsic = generic::Extrinsic<AccountId, Index, Call>;
/// Executive: handles dispatch to the various modules.
pub type Executive = executive::Executive<Runtime, Block, Balances, Balances,
	(((((), Council), Democracy), Staking), Session)>;

impl_outer_config! {
	pub struct GenesisConfig for Runtime {
		ConsensusConfig => consensus,
		SystemConfig => system,
		BalancesConfig => balances,
		SessionConfig => session,
		StakingConfig => staking,
		DemocracyConfig => democracy,
		CouncilConfig => council,
		TimestampConfig => timestamp,
	}
}

pub mod api {
	impl_stubs!(
		version => |()| super::Version::version(),
		authorities => |()| super::Consensus::authorities(),
		events => |()| super::System::events(),
		initialise_block => |header| super::Executive::initialise_block(&header),
		apply_extrinsic => |extrinsic| super::Executive::apply_extrinsic(extrinsic),
		execute_block => |block| super::Executive::execute_block(block),
		finalise_block => |()| super::Executive::finalise_block(),
		validator_count => |()| super::Session::validator_count(),
		validators => |()| super::Session::validators()
	);
}
