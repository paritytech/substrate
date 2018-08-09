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

//! The Polkadot runtime. This can be compiled with ``#[no_std]`, ready for Wasm.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;

#[cfg(feature = "std")]
extern crate serde;

#[macro_use]
extern crate substrate_runtime_io as runtime_io;

#[macro_use]
extern crate substrate_runtime_support;

#[macro_use]
extern crate substrate_runtime_primitives as runtime_primitives;

#[cfg(test)]
#[macro_use]
extern crate hex_literal;

#[cfg(test)]
extern crate substrate_serializer;

extern crate substrate_primitives;

#[macro_use]
extern crate substrate_runtime_std as rstd;

extern crate polkadot_primitives as primitives;
extern crate substrate_codec as codec;
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

#[cfg(feature = "std")]
mod checked_block;
mod parachains;
mod utils;

#[cfg(feature = "std")]
pub use checked_block::CheckedBlock;
pub use utils::{inherent_extrinsics, check_extrinsic};
pub use staking::address::Address as RawAddress;

use primitives::{AccountId, AccountIndex, Balance, BlockNumber, Hash, Index, Log, SessionKey, Signature};
use runtime_primitives::{generic, traits::{HasPublicAux, BlakeTwo256, Convert}};
use version::RuntimeVersion;

#[cfg(feature = "std")]
pub use runtime_primitives::BuildStorage;

pub use consensus::Call as ConsensusCall;
pub use timestamp::Call as TimestampCall;
pub use parachains::Call as ParachainsCall;
pub use primitives::Header;

/// The position of the timestamp set extrinsic.
pub const TIMESTAMP_SET_POSITION: u32 = 0;
/// The position of the parachains set extrinsic.
pub const PARACHAINS_SET_POSITION: u32 = 1;
/// The position of the offline nodes noting extrinsic.
pub const NOTE_OFFLINE_POSITION: u32 = 2;

/// The address format for describing accounts.
pub type Address = staking::Address<Concrete>;
/// Block Id type for this block.
pub type BlockId = generic::BlockId<Block>;
/// Unchecked extrinsic type as expected by this runtime.
pub type UncheckedExtrinsic = generic::UncheckedExtrinsic<Address, Index, Call, Signature>;
/// Extrinsic type as expected by this runtime. This is not the type that is signed.
pub type Extrinsic = generic::Extrinsic<Address, Index, Call>;
/// Extrinsic type that is signed.
pub type BareExtrinsic = generic::Extrinsic<AccountId, Index, Call>;
/// Block type as expected by this runtime.
pub type Block = generic::Block<Header, UncheckedExtrinsic>;

/// Concrete runtime type used to parameterize the various modules.
// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct Concrete;

/// Polkadot runtime version.
pub const VERSION: RuntimeVersion = RuntimeVersion {
	spec_name: ver_str!("polkadot"),
	impl_name: ver_str!("parity-polkadot"),
	authoring_version: 1,
	spec_version: 3,
	impl_version: 0,
};

impl version::Trait for Concrete {
	const VERSION: RuntimeVersion = VERSION;
}

/// Version module for this concrete runtime.
pub type Version = version::Module<Concrete>;

impl HasPublicAux for Concrete {
	type PublicAux = AccountId;	// TODO: Option<AccountId>
}

impl system::Trait for Concrete {
	type Index = Index;
	type BlockNumber = BlockNumber;
	type Hash = Hash;
	type Hashing = BlakeTwo256;
	type Digest = generic::Digest<Log>;
	type AccountId = AccountId;
	type Header = Header;
}
/// System module for this concrete runtime.
pub type System = system::Module<Concrete>;

impl consensus::Trait for Concrete {
	type PublicAux = <Concrete as HasPublicAux>::PublicAux;
	type SessionKey = SessionKey;
}
/// Consensus module for this concrete runtime.
pub type Consensus = consensus::Module<Concrete>;

impl timestamp::Trait for Concrete {
	const TIMESTAMP_SET_POSITION: u32 = TIMESTAMP_SET_POSITION;
	type Moment = u64;
}
/// Timestamp module for this concrete runtime.
pub type Timestamp = timestamp::Module<Concrete>;

/// Session key conversion.
pub struct SessionKeyConversion;
impl Convert<AccountId, SessionKey> for SessionKeyConversion {
	fn convert(a: AccountId) -> SessionKey {
		a.0.into()
	}
}

impl session::Trait for Concrete {
	const NOTE_OFFLINE_POSITION: u32 = NOTE_OFFLINE_POSITION;
	type ConvertAccountIdToSessionKey = SessionKeyConversion;
	type OnSessionChange = Staking;
}
/// Session module for this concrete runtime.
pub type Session = session::Module<Concrete>;

impl staking::Trait for Concrete {
	type Balance = Balance;
	type AccountIndex = AccountIndex;
	type OnAccountKill = ();
}
/// Staking module for this concrete runtime.
pub type Staking = staking::Module<Concrete>;

impl democracy::Trait for Concrete {
	type Proposal = PrivCall;
}
/// Democracy module for this concrete runtime.
pub type Democracy = democracy::Module<Concrete>;

impl council::Trait for Concrete {}
/// Council module for this concrete runtime.
pub type Council = council::Module<Concrete>;
/// Council voting module for this concrete runtime.
pub type CouncilVoting = council::voting::Module<Concrete>;

impl parachains::Trait for Concrete {
	const SET_POSITION: u32 = PARACHAINS_SET_POSITION;

	type PublicAux = <Concrete as HasPublicAux>::PublicAux;
}
pub type Parachains = parachains::Module<Concrete>;

impl_outer_dispatch! {
	/// Call type for polkadot transactions.
	#[derive(Clone, PartialEq, Eq)]
	#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
	pub enum Call where aux: <Concrete as HasPublicAux>::PublicAux {
		Consensus = 0,
		Session = 1,
		Staking = 2,
		Timestamp = 3,
		Democracy = 5,
		Council = 6,
		CouncilVoting = 7,
		Parachains = 8,
	}

	/// Internal calls.
	#[derive(Clone, PartialEq, Eq)]
	#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
	pub enum PrivCall {
		Consensus = 0,
		Session = 1,
		Staking = 2,
		Democracy = 5,
		Council = 6,
		CouncilVoting = 7,
		Parachains = 8,
	}
}

/// Executive: handles dispatch to the various modules.
pub type Executive = executive::Executive<Concrete, Block, Staking, Staking,
	(((((((), Parachains), Council), Democracy), Staking), Session), Timestamp)>;

impl_outer_config! {
	pub struct GenesisConfig for Concrete {
		ConsensusConfig => consensus,
		SystemConfig => system,
		SessionConfig => session,
		StakingConfig => staking,
		DemocracyConfig => democracy,
		CouncilConfig => council,
		TimestampConfig => timestamp,
		ParachainsConfig => parachains,
	}
}

pub mod api {
	impl_stubs!(
		version => |()| super::Version::version(),
		authorities => |()| super::Consensus::authorities(),
		initialise_block => |header| super::Executive::initialise_block(&header),
		apply_extrinsic => |extrinsic| super::Executive::apply_extrinsic(extrinsic),
		execute_block => |block| super::Executive::execute_block(block),
		finalise_block => |()| super::Executive::finalise_block(),
		inherent_extrinsics => |inherent| super::inherent_extrinsics(inherent),
		validator_count => |()| super::Session::validator_count(),
		validators => |()| super::Session::validators()
	);
}

#[cfg(test)]
mod tests {
	use super::*;
	use substrate_primitives as primitives;
	use codec::{Encode, Decode};
	use substrate_primitives::hexdisplay::HexDisplay;
	use substrate_serializer as ser;
	use runtime_primitives::traits::{Digest as DigestT, Header as HeaderT};
	type Digest = generic::Digest<Log>;

	#[test]
	fn test_header_serialization() {
		let header = Header {
			parent_hash: 5.into(),
			number: 67,
			state_root: 3.into(),
			extrinsics_root: 6.into(),
			digest: { let mut d = Digest::default(); d.push(Log(vec![1])); d },
		};

		assert_eq!(ser::to_string_pretty(&header), r#"{
  "parentHash": "0x0000000000000000000000000000000000000000000000000000000000000005",
  "number": 67,
  "stateRoot": "0x0000000000000000000000000000000000000000000000000000000000000003",
  "extrinsicsRoot": "0x0000000000000000000000000000000000000000000000000000000000000006",
  "digest": {
    "logs": [
      "0x01"
    ]
  }
}"#);

		let v = header.encode();
		assert_eq!(Header::decode(&mut &v[..]).unwrap(), header);
	}

	#[test]
	fn block_encoding_round_trip() {
		let mut block = Block {
			header: Header::new(1, Default::default(), Default::default(), Default::default(), Default::default()),
			extrinsics: vec![
				UncheckedExtrinsic::new(
					generic::Extrinsic {
						function: Call::Timestamp(timestamp::Call::set(100_000_000)),
						signed: Default::default(),
						index: Default::default(),
					},
					Default::default(),
				)
			],
		};

		let raw = block.encode();
		let decoded = Block::decode(&mut &raw[..]).unwrap();

		assert_eq!(block, decoded);

		block.extrinsics.push(UncheckedExtrinsic::new(
			generic::Extrinsic {
				function: Call::Staking(staking::Call::stake()),
				signed: Default::default(),
				index: 10101,
			},
			Default::default(),
		));

		let raw = block.encode();
		let decoded = Block::decode(&mut &raw[..]).unwrap();

		assert_eq!(block, decoded);
	}

	#[test]
	fn block_encoding_substrate_round_trip() {
		let mut block = Block {
			header: Header::new(1, Default::default(), Default::default(), Default::default(), Default::default()),
			extrinsics: vec![
				UncheckedExtrinsic::new(
					generic::Extrinsic {
						function: Call::Timestamp(timestamp::Call::set(100_000_000)),
						signed: Default::default(),
						index: Default::default(),
					},
					Default::default(),
				)
			],
		};

		block.extrinsics.push(UncheckedExtrinsic::new(
			generic::Extrinsic {
				function: Call::Staking(staking::Call::stake()),
				signed: Default::default(),
				index: 10101,
			},
			Default::default()
		));

		let raw = block.encode();
		let decoded_primitive = ::primitives::Block::decode(&mut &raw[..]).unwrap();
		let encoded_primitive = decoded_primitive.encode();
		let decoded = Block::decode(&mut &encoded_primitive[..]).unwrap();

		assert_eq!(block, decoded);
	}

	#[test]
	fn serialize_unchecked() {
		let tx = UncheckedExtrinsic::new(
			Extrinsic {
				signed: AccountId::from([1; 32]).into(),
				index: 999,
				function: Call::Timestamp(TimestampCall::set(135135)),
			},
			runtime_primitives::Ed25519Signature(primitives::hash::H512([0; 64])).into()
		);

		// 6f000000
		// ff0101010101010101010101010101010101010101010101010101010101010101
		// e7030000
		// 0300
		// df0f0200
		// 0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

		let v = Encode::encode(&tx);
		assert_eq!(&v[..], &hex!["6f000000ff0101010101010101010101010101010101010101010101010101010101010101e70300000300df0f02000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"][..]);
		println!("{}", HexDisplay::from(&v));
		assert_eq!(UncheckedExtrinsic::decode(&mut &v[..]).unwrap(), tx);
	}

	#[test]
	fn serialize_checked() {
		let xt = Extrinsic {
			signed: AccountId::from(hex!["0d71d1a9cad6f2ab773435a7dec1bac019994d05d1dd5eb3108211dcf25c9d1e"]).into(),
			index: 0,
			function: Call::CouncilVoting(council::voting::Call::propose(Box::new(
				PrivCall::Consensus(consensus::PrivCall::set_code(
					vec![]
				))
			))),
		};
		let v = Encode::encode(&xt);
		assert_eq!(Extrinsic::decode(&mut &v[..]).unwrap(), xt);
	}

	#[test]
	fn parachain_calls_are_privcall() {
		let _register = PrivCall::Parachains(parachains::PrivCall::register_parachain(0.into(), vec![1, 2, 3], vec![]));
		let _deregister = PrivCall::Parachains(parachains::PrivCall::deregister_parachain(0.into()));
	}
}
