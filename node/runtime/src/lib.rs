// Copyright 2018 Parity Technologies (UK) Ltd.
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

//! The Substrate runtime. This can be compiled with ``#[no_std]`, ready for Wasm.

#![cfg_attr(not(feature = "std"), no_std)]
// `construct_runtime!` does a lot of recursion and requires us to increase the limit to 256.
#![recursion_limit="256"]

#[macro_use]
extern crate sr_io as runtime_io;

#[macro_use]
extern crate srml_support;

#[macro_use]
extern crate sr_primitives as runtime_primitives;

#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;

extern crate substrate_primitives;

#[macro_use]
extern crate parity_codec_derive;

#[cfg_attr(not(feature = "std"), macro_use)]
extern crate sr_std as rstd;
extern crate srml_balances as balances;
extern crate srml_consensus as consensus;
extern crate srml_contract as contract;
extern crate srml_council as council;
extern crate srml_democracy as democracy;
extern crate srml_executive as executive;
extern crate srml_session as session;
extern crate srml_staking as staking;
extern crate srml_system as system;
extern crate srml_timestamp as timestamp;
extern crate srml_treasury as treasury;
#[macro_use]
extern crate sr_version as version;
extern crate node_primitives;

#[cfg(feature = "std")]
mod checked_block;

use rstd::prelude::*;
use substrate_primitives::u32_trait::{_2, _4};
use node_primitives::{AccountId, AccountIndex, Balance, BlockNumber, Hash, Index, SessionKey, Signature, InherentData};
use runtime_primitives::generic;
use runtime_primitives::traits::{Convert, BlakeTwo256, DigestItem};
use version::{RuntimeVersion, ApiId};
use council::{motions as council_motions, voting as council_voting};
#[cfg(any(feature = "std", test))]
use version::NativeVersion;

#[cfg(any(feature = "std", test))]
pub use runtime_primitives::BuildStorage;
pub use consensus::Call as ConsensusCall;
pub use timestamp::Call as TimestampCall;
pub use balances::Call as BalancesCall;
pub use runtime_primitives::{Permill, Perbill};
pub use timestamp::BlockPeriod;
pub use srml_support::StorageValue;
#[cfg(any(feature = "std", test))]
pub use checked_block::CheckedBlock;

const TIMESTAMP_SET_POSITION: u32 = 0;
const NOTE_OFFLINE_POSITION: u32 = 1;

const INHERENT: ApiId = *b"inherent";
const VALIDATX: ApiId = *b"validatx";

/// Runtime version.
pub const VERSION: RuntimeVersion = RuntimeVersion {
	spec_name: ver_str!("node"),
	impl_name: ver_str!("substrate-node"),
	authoring_version: 1,
	spec_version: 1,
	impl_version: 0,
	apis: apis_vec!([(INHERENT, 1), (VALIDATX, 1)]),
};

/// Native version.
#[cfg(any(feature = "std", test))]
pub fn native_version() -> NativeVersion {
	NativeVersion {
		runtime_version: VERSION,
		can_author_with: Default::default(),
	}
}

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
	type Log = Log;
}

impl balances::Trait for Runtime {
	type Balance = Balance;
	type AccountIndex = AccountIndex;
	type OnFreeBalanceZero = (Staking, Contract);
	type EnsureAccountLiquid = Staking;
	type Event = Event;
}

impl consensus::Trait for Runtime {
	const NOTE_OFFLINE_POSITION: u32 = NOTE_OFFLINE_POSITION;
	type Log = Log;
	type SessionKey = SessionKey;
	type OnOfflineValidator = Staking;
}

impl timestamp::Trait for Runtime {
	const TIMESTAMP_SET_POSITION: u32 = TIMESTAMP_SET_POSITION;
	type Moment = u64;
}

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

impl staking::Trait for Runtime {
	type OnRewardMinted = Treasury;
	type Event = Event;
}

impl democracy::Trait for Runtime {
	type Proposal = Call;
	type Event = Event;
}

impl council::Trait for Runtime {
	type Event = Event;
}

impl council::voting::Trait for Runtime {
	type Event = Event;
}

impl council::motions::Trait for Runtime {
	type Origin = Origin;
	type Proposal = Call;
	type Event = Event;
}

impl treasury::Trait for Runtime {
	type ApproveOrigin = council_motions::EnsureMembers<_4>;
	type RejectOrigin = council_motions::EnsureMembers<_2>;
	type Event = Event;
}

impl contract::Trait for Runtime {
	type Gas = u64;
	type DetermineContractAddress = contract::SimpleAddressDeterminator<Runtime>;
	type Event = Event;
}

impl DigestItem for Log {
	type Hash = Hash;
	type AuthorityId = SessionKey;

	fn as_authorities_change(&self) -> Option<&[Self::AuthorityId]> {
		match self.0 {
			InternalLog::consensus(ref item) => item.as_authorities_change(),
			_ => None,
		}
	}

	fn as_changes_trie_root(&self) -> Option<&Self::Hash> {
		match self.0 {
			InternalLog::system(ref item) => item.as_changes_trie_root(),
			_ => None,
		}
	}
}

construct_runtime!(
	pub enum Runtime with Log(InternalLog: DigestItem<Hash, SessionKey>) {
		System: system::{default, Log(ChangesTrieRoot)},
		Consensus: consensus::{Module, Call, Storage, Config, Log(AuthoritiesChange)},
		Balances: balances,
		Timestamp: timestamp::{Module, Call, Storage, Config},
		Session: session,
		Staking: staking,
		Democracy: democracy,
		Council: council,
		CouncilVoting: council_voting::{Module, Call, Storage, Event<T>},
		CouncilMotions: council_motions::{Module, Call, Storage, Event<T>, Origin},
		Treasury: treasury,
		Contract: contract::{Module, Call, Config, Event<T>},
	}
);

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
pub type UncheckedExtrinsic = generic::UncheckedMortalExtrinsic<Address, Index, Call, Signature>;
/// Extrinsic type that has already been checked.
pub type CheckedExtrinsic = generic::CheckedExtrinsic<AccountId, Index, Call>;
/// Executive: handles dispatch to the various modules.
pub type Executive = executive::Executive<Runtime, Block, balances::ChainContext<Runtime>, Balances, AllModules>;

pub mod api {
	impl_stubs!(
		version => |()| super::VERSION,
		metadata => |()| super::Runtime::metadata(),
		authorities => |()| super::Consensus::authorities(),
		initialise_block => |header| super::Executive::initialise_block(&header),
		apply_extrinsic => |extrinsic| super::Executive::apply_extrinsic(extrinsic),
		execute_block => |block| super::Executive::execute_block(block),
		finalise_block => |()| super::Executive::finalise_block(),
		inherent_extrinsics => |inherent| super::inherent_extrinsics(inherent),
		validator_count => |()| super::Session::validator_count(),
		validators => |()| super::Session::validators(),
		timestamp => |()| super::Timestamp::get(),
		random_seed => |()| super::System::random_seed(),
		account_nonce => |account| super::System::account_nonce(&account),
		lookup_address => |address| super::Balances::lookup_address(address),
		validate_transaction => |tx| super::Executive::validate_transaction(tx)
	);
}

/// Produces the list of inherent extrinsics.
fn inherent_extrinsics(data: InherentData) -> Vec<UncheckedExtrinsic> {
	let mut inherent = vec![generic::UncheckedMortalExtrinsic::new_unsigned(
		Call::Timestamp(TimestampCall::set(data.timestamp))
	)];

	if !data.offline_indices.is_empty() {
		inherent.push(generic::UncheckedMortalExtrinsic::new_unsigned(
			Call::Consensus(ConsensusCall::note_offline(data.offline_indices))
		));
	}

	inherent
}
