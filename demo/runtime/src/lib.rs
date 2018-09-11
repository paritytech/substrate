// Copyright 2018 Parity Technologies (UK) Ltd.
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
extern crate substrate_primitives;

#[macro_use]
extern crate substrate_codec_derive;

#[cfg_attr(not(feature = "std"), macro_use)]
extern crate substrate_runtime_std as rstd;
extern crate substrate_runtime_balances as balances;
extern crate substrate_runtime_consensus as consensus;
extern crate substrate_runtime_contract as contract;
extern crate substrate_runtime_council as council;
extern crate substrate_runtime_democracy as democracy;
extern crate substrate_runtime_executive as executive;
extern crate substrate_runtime_session as session;
extern crate substrate_runtime_staking as staking;
extern crate substrate_runtime_system as system;
extern crate substrate_runtime_timestamp as timestamp;
extern crate substrate_runtime_treasury as treasury;
#[macro_use]
extern crate substrate_runtime_version as version;
extern crate demo_primitives;

#[cfg(feature = "std")]
mod checked_block;

use rstd::prelude::*;
use substrate_primitives::u32_trait::{_2, _4};
use codec::{Encode, Decode, Input};
use demo_primitives::{AccountId, AccountIndex, Balance, BlockNumber, Hash, Index, SessionKey, Signature, InherentData};
use runtime_primitives::generic;
use runtime_primitives::traits::{Convert, BlakeTwo256, DigestItem};
use version::RuntimeVersion;
use council::{motions as council_motions, voting as council_voting};

#[cfg(any(feature = "std", test))]
pub use runtime_primitives::BuildStorage;
pub use consensus::Call as ConsensusCall;
pub use timestamp::Call as TimestampCall;
pub use runtime_primitives::Permill;
#[cfg(any(feature = "std", test))]
pub use checked_block::CheckedBlock;

const TIMESTAMP_SET_POSITION: u32 = 0;
const NOTE_OFFLINE_POSITION: u32 = 1;

// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
/// Runtime type used to collate and parameterize the various modules.
pub struct Runtime;

/// Runtime version.
pub const VERSION: RuntimeVersion = RuntimeVersion {
	spec_name: ver_str!("demo"),
	impl_name: ver_str!("substrate-demo"),
	authoring_version: 1,
	spec_version: 1,
	impl_version: 0,
};

impl system::Trait for Runtime {
	type Origin = Origin;
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
	type OnFreeBalanceZero = (Staking, Contract);
	type EnsureAccountLiquid = Staking;
	type Event = Event;
}

/// Staking module for this concrete runtime.
pub type Balances = balances::Module<Runtime>;

impl consensus::Trait for Runtime {
	const NOTE_OFFLINE_POSITION: u32 = NOTE_OFFLINE_POSITION;
	type Log = Log;
	type SessionKey = SessionKey;
	type OnOfflineValidator = Staking;
}

/// Consensus module for this concrete runtime.
pub type Consensus = consensus::Module<Runtime>;

impl timestamp::Trait for Runtime {
	const TIMESTAMP_SET_POSITION: u32 = TIMESTAMP_SET_POSITION;
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
	type OnRewardMinted = Treasury;
	type Event = Event;
}

/// Staking module for this concrete runtime.
pub type Staking = staking::Module<Runtime>;

impl democracy::Trait for Runtime {
	type Proposal = Call;
	type Event = Event;
}

/// Democracy module for this concrete runtime.
pub type Democracy = democracy::Module<Runtime>;

impl council::Trait for Runtime {
	type Event = Event;
}

/// Council module for this concrete runtime.
pub type Council = council::Module<Runtime>;

impl council::voting::Trait for Runtime {
	type Event = Event;
}

/// Council voting module for this concrete runtime.
pub type CouncilVoting = council::voting::Module<Runtime>;

impl council::motions::Trait for Runtime {
	type Origin = Origin;
	type Proposal = Call;
	type Event = Event;
}

/// Council motions module for this concrete runtime.
pub type CouncilMotions = council_motions::Module<Runtime>;

impl treasury::Trait for Runtime {
	type ApproveOrigin = council_motions::EnsureMembers<_4>;
	type RejectOrigin = council_motions::EnsureMembers<_2>;
	type Event = Event;
}

/// Treasury module for this concrete runtime.
pub type Treasury = treasury::Module<Runtime>;

/// Address calculated from the code (of the constructor), input data to the constructor
/// and account id which requested the account creation.
///
/// Formula: `blake2_256(blake2_256(code) + blake2_256(data) + origin)`
pub struct DetermineContractAddress;
impl contract::ContractAddressFor<AccountId> for DetermineContractAddress {
	fn contract_address_for(code: &[u8], data: &[u8], origin: &AccountId) -> AccountId {
		use runtime_primitives::traits::Hash;

		let code_hash = BlakeTwo256::hash(code);
		let data_hash = BlakeTwo256::hash(data);
		let mut buf = [0u8, 32 + 32 + 32];
		&mut buf[0..32].copy_from_slice(&code_hash);
		&mut buf[32..64].copy_from_slice(&data_hash);
		&mut buf[64..96].copy_from_slice(origin);
		AccountId::from(BlakeTwo256::hash(&buf[..]))
	}
}

impl contract::Trait for Runtime {
	type Gas = u64;
	type DetermineContractAddress = DetermineContractAddress;
}

/// Contract module for this concrete runtime.
pub type Contract = contract::Module<Runtime>;

impl_outer_event! {
	pub enum Event for Runtime {
		//consensus,
		balances,
		//timetstamp,
		session,
		staking,
		democracy,
		council,
		council_voting,
		council_motions,
		treasury
	}
}

impl_outer_log! {
	pub enum Log(InternalLog: DigestItem<SessionKey>) for Runtime {
		consensus(AuthoritiesChange)
	}
}

impl_outer_origin! {
	pub enum Origin for Runtime {
		council_motions
	}
}

impl_outer_dispatch! {
	pub enum Call where origin: Origin {
		Consensus,
		Balances,
		Timestamp,
		Session,
		Staking,
		Democracy,
		Council,
		CouncilVoting,
		CouncilMotions,
		Treasury,
		Contract,
	}
}

impl_outer_config! {
	pub struct GenesisConfig for Runtime {
		SystemConfig => system,
		ConsensusConfig => consensus,
		ContractConfig => contract,
		BalancesConfig => balances,
		TimestampConfig => timestamp,
		SessionConfig => session,
		StakingConfig => staking,
		DemocracyConfig => democracy,
		CouncilConfig => council,
		TreasuryConfig => treasury,
	}
}

type AllModules = (
	Consensus,
	Balances,
	Timestamp,
	Session,
	Staking,
	Democracy,
	Council,
	CouncilVoting,
	CouncilMotions,
	Treasury,
	Contract,
);

impl_json_metadata!(
	for Runtime with modules
		system::Module with Storage,
		consensus::Module with Storage,
		balances::Module with Storage,
		timestamp::Module with Storage,
		session::Module with Storage,
		staking::Module with Storage,
		democracy::Module with Storage,
		council::Module with Storage,
		council_voting::Module with Storage,
		council_motions::Module with Storage,
		treasury::Module with Storage,
		contract::Module with Storage,
);

impl DigestItem for Log {
	type AuthorityId = SessionKey;

	fn as_authorities_change(&self) -> Option<&[Self::AuthorityId]> {
		match self.0 {
			InternalLog::consensus(ref item) => item.as_authorities_change(),
		}
	}
}

/// The address format for describing accounts.
pub use balances::address::Address as RawAddress;
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
/// Extrinsic type that has already been checked.
pub type CheckedExtrinsic = generic::CheckedExtrinsic<AccountId, Index, Call>;
/// Executive: handles dispatch to the various modules.
pub type Executive = executive::Executive<Runtime, Block, Balances, Balances, AllModules>;

pub mod api {
	impl_stubs!(
		version => |()| super::VERSION,
		json_metadata => |()| super::Runtime::json_metadata(),
		authorities => |()| super::Consensus::authorities(),
		initialise_block => |header| super::Executive::initialise_block(&header),
		apply_extrinsic => |extrinsic| super::Executive::apply_extrinsic(extrinsic),
		execute_block => |block| super::Executive::execute_block(block),
		finalise_block => |()| super::Executive::finalise_block(),
		inherent_extrinsics => |(inherent, spec_version)| super::inherent_extrinsics(inherent, spec_version),
		validator_count => |()| super::Session::validator_count(),
		validators => |()| super::Session::validators(),
		timestamp => |()| super::Timestamp::get(),
		random_seed => |()| super::System::random_seed(),
		account_nonce => |account| super::System::account_nonce(&account),
		lookup_address => |address| super::Balances::lookup_address(address)
	);
}

/// Produces the list of inherent extrinsics.
fn inherent_extrinsics(data: InherentData, _spec_version: u32) -> Vec<UncheckedExtrinsic> {
	let make_inherent = |function| UncheckedExtrinsic {
		signature: Default::default(),
		function,
		index: 0,
	};

	let mut inherent = vec![
		make_inherent(Call::Timestamp(TimestampCall::set(data.timestamp))),
	];

	if !data.offline_indices.is_empty() {
		inherent.push(make_inherent(
				Call::Consensus(ConsensusCall::note_offline(data.offline_indices))
		));
	}

	inherent
}
