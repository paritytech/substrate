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

//! Strongly typed API for Polkadot based around the locally-compiled native
//! runtime.

extern crate polkadot_executor;
extern crate polkadot_runtime as runtime;
extern crate polkadot_primitives as primitives;
extern crate substrate_codec as codec;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_client as client;
extern crate substrate_executor as substrate_executor;
extern crate substrate_runtime_executive;
extern crate substrate_primitives;
extern crate substrate_state_machine as state_machine;

#[macro_use]
extern crate error_chain;

#[cfg(test)]
extern crate substrate_keyring as keyring;

pub mod full;
pub mod light;

use primitives::{AccountId, BlockId, Hash, Index, SessionKey, Timestamp};
use primitives::parachain::DutyRoster;
use runtime::{Block, UncheckedExtrinsic};

error_chain! {
	errors {
		/// Unknown runtime code.
		UnknownRuntime {
			description("Unknown runtime code")
			display("Unknown runtime code")
		}
		/// Unknown block ID.
		UnknownBlock(b: BlockId) {
			description("Unknown block")
			display("Unknown block")
		}
		/// Attempted to push an inherent extrinsic manually.
		PushedInherentTransaction(xt: UncheckedExtrinsic) {
			description("Attempted to push an inherent extrinsic to a block."),
			display("Pushed inherent extrinsic to a block: {:?}", xt),
		}
		/// Badly-formed extrinsic.
		BadlyFormedTransaction(xt: UncheckedExtrinsic) {
			description("Attempted to push a badly-formed extrinsic to a block."),
			display("Pushed badly-formed extrinsic to a block: {:?}", xt),
		}
		/// Some other error.
		// TODO: allow to be specified as associated type of PolkadotApi
		Other(e: Box<::std::error::Error + Send>) {
			description("Other error")
			display("Other error: {}", e.description())
		}
	}

	links {
		Executor(substrate_executor::error::Error, substrate_executor::error::ErrorKind);
	}
}

impl From<client::error::Error> for Error {
	fn from(e: client::error::Error) -> Error {
		match e {
			client::error::Error(client::error::ErrorKind::UnknownBlock(b), _) => Error::from_kind(ErrorKind::UnknownBlock(b)),
			other => Error::from_kind(ErrorKind::Other(Box::new(other) as Box<_>)),
		}
	}
}

/// A builder for blocks.
pub trait BlockBuilder: Sized {
	/// Push a non-inherent extrinsic.
	fn push_extrinsic(&mut self, extrinsic: UncheckedExtrinsic) -> Result<()>;

	/// Finalise the block.
	fn bake(self) -> Block;
}

/// A checked block identifier.
pub trait CheckedBlockId: Clone + 'static {
	/// Yield the underlying block ID.
	fn block_id(&self) -> &BlockId;
}

/// Trait encapsulating the Polkadot API.
///
/// All calls should fail when the exact runtime is unknown.
pub trait PolkadotApi {
	/// A checked block ID. Used to avoid redundancy of code check.
	type CheckedBlockId: CheckedBlockId;
	/// The type used to build blocks.
	type BlockBuilder: BlockBuilder;

	/// Check whether requests at the given block ID can be served.
	///
	/// It should not be possible to instantiate this type without going
	/// through this function.
	fn check_id(&self, id: BlockId) -> Result<Self::CheckedBlockId>;

	/// Get session keys at a given block.
	fn session_keys(&self, at: &Self::CheckedBlockId) -> Result<Vec<SessionKey>>;

	/// Get validators at a given block.
	fn validators(&self, at: &Self::CheckedBlockId) -> Result<Vec<AccountId>>;

	/// Get the value of the randomness beacon at a given block.
	fn random_seed(&self, at: &Self::CheckedBlockId) -> Result<Hash>;

	/// Get the authority duty roster at a block.
	fn duty_roster(&self, at: &Self::CheckedBlockId) -> Result<DutyRoster>;

	/// Get the timestamp registered at a block.
	fn timestamp(&self, at: &Self::CheckedBlockId) -> Result<Timestamp>;

	/// Get the index of an account at a block.
	fn index(&self, at: &Self::CheckedBlockId, account: AccountId) -> Result<Index>;


	/// Evaluate a block and see if it gives an error.
	fn evaluate_block(&self, at: &Self::CheckedBlockId, block: Block) -> Result<()>;

	/// Create a block builder on top of the parent block.
	fn build_block(&self, parent: &Self::CheckedBlockId, timestamp: u64) -> Result<Self::BlockBuilder>;
}

/// Mark for all Polkadot API implementations, that are making use of state data, stored locally.
pub trait LocalPolkadotApi: PolkadotApi {}

/// Mark for all Polkadot API implementations, that are fetching required state data from remote nodes.
pub trait RemotePolkadotApi: PolkadotApi {}


#[cfg(test)]
mod tests {
	use super::*;
	use keyring::Keyring;
	use codec::Slicable;
	use client::{self, LocalCallExecutor};
	use client::in_mem::Backend as InMemory;
	use substrate_executor::NativeExecutionDispatch;
	use substrate_primitives::Header;
	use runtime::{GenesisConfig, ConsensusConfig, SessionConfig, BuildExternalities};

	fn validators() -> Vec<AccountId> {
		vec![
			Keyring::One.to_raw_public(),
			Keyring::Two.to_raw_public(),
		]
	}

	fn client() -> Client<InMemory, LocalCallExecutor<InMemory, NativeExecutor<LocalDispatch>>> {
		struct GenesisBuilder;

		impl client::GenesisBuilder for GenesisBuilder {
			fn build(self) -> (Header, Vec<(Vec<u8>, Vec<u8>)>) {
				let genesis_config = GenesisConfig {
					consensus: Some(ConsensusConfig {
						code: LocalDispatch::native_equivalent().to_vec(),
						authorities: validators(),
					}),
					system: None,
					session: Some(SessionConfig {
						validators: validators(),
						session_length: 100,
					}),
					council: Some(Default::default()),
					democracy: Some(Default::default()),
					parachains: Some(Default::default()),
					staking: Some(Default::default()),
				};

				let storage = genesis_config.build_externalities();
				let block = ::client::genesis::construct_genesis_block(&storage);
				(substrate_primitives::block::Header::decode(&mut block.header.encode().as_ref()).expect("to_vec() always gives a valid serialisation; qed"), storage.into_iter().collect())
			}
		}

		::client::new_in_mem(LocalDispatch::new(), GenesisBuilder).unwrap()
	}

	#[test]
	fn gets_session_and_validator_keys() {
		let client = client();
		let id = client.check_id(BlockId::Number(0)).unwrap();
		assert_eq!(client.session_keys(&id).unwrap(), validators());
		assert_eq!(client.validators(&id).unwrap(), validators());
	}

	#[test]
	fn build_block() {
		let client = client();

		let id = client.check_id(BlockId::Number(0)).unwrap();
		let block_builder = client.build_block(&id, 1_000_000).unwrap();
		let block = block_builder.bake();

		assert_eq!(block.header.number, 1);
		assert!(block.header.extrinsics_root != Default::default());
	}

	#[test]
	fn fails_to_check_id_for_unknown_block() {
		assert!(client().check_id(BlockId::Number(100)).is_err());
	}

	#[test]
	fn gets_random_seed_with_genesis() {
		let client = client();

		let id = client.check_id(BlockId::Number(0)).unwrap();
		assert!(client.random_seed(&id).is_ok());
	}
}
