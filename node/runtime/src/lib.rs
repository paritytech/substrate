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
extern crate sr_api as runtime_api;

#[macro_use]
extern crate srml_support;

#[macro_use]
extern crate sr_primitives as runtime_primitives;

#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;

extern crate substrate_primitives;

#[cfg(feature = "std")]
extern crate substrate_client as client;

#[macro_use]
extern crate parity_codec_derive;

extern crate parity_codec as codec;

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
extern crate srml_upgrade_key as upgrade_key;
#[macro_use]
extern crate sr_version as version;
extern crate node_primitives;

use codec::{Encode, Decode};
use rstd::prelude::*;
use substrate_primitives::u32_trait::{_2, _4};
use node_primitives::{
	AccountId, AccountIndex, Balance, BlockNumber, Hash, Index,
	SessionKey, Signature, Block as GBlock,
};
use runtime_api::{runtime::*, id::*};
use runtime_primitives::ApplyResult;
use runtime_primitives::transaction_validity::TransactionValidity;
use runtime_primitives::generic;
use runtime_primitives::traits::{Convert, BlakeTwo256, Block as BlockT, Api};
use substrate_primitives::AuthorityId;
use version::RuntimeVersion;
use council::{motions as council_motions, voting as council_voting};
#[cfg(feature = "std")]
use council::seats as council_seats;
#[cfg(any(feature = "std", test))]
use version::NativeVersion;

#[cfg(any(feature = "std", test))]
pub use runtime_primitives::BuildStorage;
pub use consensus::Call as ConsensusCall;
pub use timestamp::Call as TimestampCall;
pub use balances::Call as BalancesCall;
pub use runtime_primitives::{Permill, Perbill};
pub use timestamp::BlockPeriod;
pub use srml_support::{StorageValue, RuntimeMetadata};

const TIMESTAMP_SET_POSITION: u32 = 0;
const NOTE_OFFLINE_POSITION: u32 = 1;

/// Runtime version.
pub const VERSION: RuntimeVersion = RuntimeVersion {
	spec_name: ver_str!("node"),
	impl_name: ver_str!("substrate-node"),
	authoring_version: 1,
	spec_version: 1,
	impl_version: 0,
	apis: apis_vec!([
		(BLOCK_BUILDER, 1),
		(TAGGED_TRANSACTION_QUEUE, 1),
		(METADATA, 1)
	]),
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
		a.to_fixed_bytes().into()
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

impl upgrade_key::Trait for Runtime {
	type Event = Event;
}

construct_runtime!(
	pub enum Runtime with Log(InternalLog: DigestItem<Hash, SessionKey>) where
		Block = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: system::{default, Log(ChangesTrieRoot)},
		Timestamp: timestamp::{Module, Call, Storage, Config<T>, Inherent},
		Consensus: consensus::{Module, Call, Storage, Config<T>, Log(AuthoritiesChange), Inherent},
		Balances: balances,
		Session: session,
		Staking: staking,
		Democracy: democracy,
		Council: council::{Module, Call, Storage, Event<T>},
		CouncilVoting: council_voting,
		CouncilMotions: council_motions::{Module, Call, Storage, Event<T>, Origin},
		CouncilSeats: council_seats::{Config<T>},
		Treasury: treasury,
		Contract: contract::{Module, Call, Config<T>, Event<T>},
		UpgradeKey: upgrade_key,
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
/// A Block signed with a Justification
pub type SignedBlock = generic::SignedBlock<Block>;
/// BlockId type as expected by this runtime.
pub type BlockId = generic::BlockId<Block>;
/// Unchecked extrinsic type as expected by this runtime.
pub type UncheckedExtrinsic = generic::UncheckedMortalExtrinsic<Address, Index, Call, Signature>;
/// Extrinsic type that has already been checked.
pub type CheckedExtrinsic = generic::CheckedExtrinsic<AccountId, Index, Call>;
/// Executive: handles dispatch to the various modules.
pub type Executive = executive::Executive<Runtime, Block, balances::ChainContext<Runtime>, Balances, AllModules>;

//TODO: Auto impl
#[cfg(feature = "std")]
pub struct ClientWithApi {
	call: *const client::runtime_api::CallIntoRuntime<Block=GBlock>,
}

#[cfg(feature = "std")]
unsafe impl Send for ClientWithApi {}
#[cfg(feature = "std")]
unsafe impl Sync for ClientWithApi {}

#[cfg(feature = "std")]
fn decode<R: Decode>(data: Vec<u8>) -> R {
	R::decode(&mut &data[..]).unwrap()
}

#[cfg(feature = "std")]
impl client::runtime_api::ConstructRuntimeApi for ClientWithApi {
	type Block = GBlock;

	fn construct_runtime_api<'a, T: client::runtime_api::CallIntoRuntime<Block=GBlock>>(call: &'a T) -> Api<'a, Self> {
		ClientWithApi { call: unsafe { ::std::mem::transmute(call as &client::runtime_api::CallIntoRuntime<Block=GBlock>) } }.into()
	}
}

type GBlockId = generic::BlockId<GBlock>;

#[cfg(feature = "std")]
impl client::runtime_api::Core<GBlock, AuthorityId> for ClientWithApi {
	type Error = client::error::Error;
	type OverlayedChanges = client::runtime_api::OverlayedChanges;

	fn version(&self, at: &GBlockId) -> Result<RuntimeVersion, Self::Error> {
		unsafe { (*self.call).call_api_at(at, "version", Vec::new()).map(decode) }
	}

	fn authorities(&self, at: &GBlockId) -> Result<Vec<AuthorityId>, Self::Error> {
		unsafe { (*self.call).call_api_at(at, "authorities", Vec::new()).map(decode) }
	}

	fn execute_block(&self, at: &GBlockId, block: &GBlock) -> Result<(), Self::Error> {
		unsafe { (*self.call).call_api_at(at, "execute_block", block.encode()).map(decode) }
	}

	fn initialise_block(&self, at: &GBlockId, overlay: &mut client::runtime_api::OverlayedChanges, header: &<GBlock as BlockT>::Header) -> Result<(), Self::Error> {
		unsafe { (*self.call).call_at_state(at, "initialise_block", header.encode(), overlay).map(decode) }
	}
}

#[cfg(feature = "std")]
impl client::runtime_api::BlockBuilder<GBlock> for ClientWithApi {
	type Error = client::error::Error;
	type OverlayedChanges = client::runtime_api::OverlayedChanges;

	fn apply_extrinsic(&self, at: &GBlockId, overlay: &mut client::runtime_api::OverlayedChanges, extrinsic: &<GBlock as BlockT>::Extrinsic) -> Result<ApplyResult, Self::Error> {
		unsafe { (*self.call).call_at_state(at, "apply_extrinsic", extrinsic.encode(), overlay).map(decode) }
	}

	fn finalise_block(&self, at: &GBlockId, overlay: &mut client::runtime_api::OverlayedChanges) -> Result<<GBlock as BlockT>::Header, Self::Error> {
		unsafe { (*self.call).call_at_state(at, "finalise_block", Vec::new(), overlay).map(decode) }
	}

	fn inherent_extrinsics<Inherent: Decode + Encode, Unchecked: Decode + Encode>(
		&self, at: &GBlockId, inherent: &Inherent
	) -> Result<Vec<Unchecked>, Self::Error> {
		unsafe { (*self.call).call_api_at(at, "inherent_extrinsics", inherent.encode()).map(decode) }
	}

	fn check_inherents<Inherent: Decode + Encode, Error: Decode + Encode>(&self, at: &GBlockId, block: &GBlock, inherent: &Inherent) -> Result<Result<(), Error>, Self::Error> {
		unsafe { (*self.call).call_api_at(at, "check_inherents", (block, inherent).encode()).map(decode) }
	}

	fn random_seed(&self, at: &GBlockId) -> Result<<GBlock as BlockT>::Hash, Self::Error> {
		unsafe { (*self.call).call_api_at(at, "random_seed", Vec::new()).map(decode) }
	}
}

#[cfg(feature = "std")]
impl client::runtime_api::TaggedTransactionQueue<GBlock> for ClientWithApi {
	type Error = client::error::Error;

	fn validate_transaction<TransactionValidity: Encode + Decode>(
		&self,
		at: &GBlockId,
		utx: &<GBlock as BlockT>::Extrinsic
	) -> Result<TransactionValidity, Self::Error> {
		unsafe { (*self.call).call_api_at(at, "validate_transaction", utx.encode()).map(decode) }
	}
}

//TODO: We can not use `Vec<u8>` here. We need to introduce a new OpaqueType,
// that just decodes by returning the input bytes.
#[cfg(feature = "std")]
impl client::runtime_api::Metadata<GBlock, Vec<u8>> for ClientWithApi {
	type Error = client::error::Error;

	fn metadata(&self, at: &GBlockId,) -> Result<Vec<u8>, Self::Error> {
		unsafe { (*self.call).call_api_at(at, "metadata", ().encode()).map(decode) }
	}
}

impl_apis! {
	impl Core<Block, SessionKey> for Runtime {
		fn version() -> RuntimeVersion {
			VERSION
		}

		fn authorities() -> Vec<SessionKey> {
			Consensus::authorities()
		}

		fn execute_block(block: Block) {
			Executive::execute_block(block)
		}

		fn initialise_block(header: <Block as BlockT>::Header) {
			Executive::initialise_block(&header)
		}
	}

	impl Metadata<RuntimeMetadata> for Runtime {
		fn metadata() -> RuntimeMetadata {
			Runtime::metadata()
		}
	}

	impl BlockBuilder<Block, InherentData, UncheckedExtrinsic, InherentData, InherentError> for Runtime {
		fn apply_extrinsic(extrinsic: <Block as BlockT>::Extrinsic) -> ApplyResult {
			Executive::apply_extrinsic(extrinsic)
		}

		fn finalise_block() -> <Block as BlockT>::Header {
			Executive::finalise_block()
		}

		fn inherent_extrinsics(data: InherentData) -> Vec<UncheckedExtrinsic> {
			data.create_inherent_extrinsics()
		}

		fn check_inherents(block: Block, data: InherentData) -> Result<(), InherentError> {
			data.check_inherents(block)
		}

		fn random_seed() -> <Block as BlockT>::Hash {
			System::random_seed()
		}
	}

	impl TaggedTransactionQueue<Block, TransactionValidity> for Runtime {
		fn validate_transaction(tx: <Block as BlockT>::Extrinsic) -> TransactionValidity {
			Executive::validate_transaction(tx)
		}
	}
}
