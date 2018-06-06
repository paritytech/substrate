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

//! Strongly typed API for full Polkadot client.

use client::backend::{Backend, LocalBackend};
use client::block_builder::BlockBuilder as ClientBlockBuilder;
use client::{Client, LocalCallExecutor};
use polkadot_executor::Executor as LocalDispatch;
use substrate_executor::{NativeExecutionDispatch, NativeExecutor};
use state_machine;

use primitives::{AccountId, Block, Header, BlockId, Hash, Index, SessionKey, Timestamp, UncheckedExtrinsic};
use primitives::parachain::{CandidateReceipt, DutyRoster, Id as ParaId};

use {CheckedBlockId, BlockBuilder, PolkadotApi, LocalPolkadotApi, ErrorKind, Error, Result};

/// A checked block ID used for the substrate-client implementation of CheckedBlockId;
#[derive(Debug, Clone, Copy)]
pub struct CheckedId(pub(crate) BlockId);

impl CheckedBlockId for CheckedId {
	fn block_id(&self) -> &BlockId {
		&self.0
	}
}

// set up the necessary scaffolding to execute a set of calls to the runtime.
// this creates a new block on top of the given ID and initialises it.
macro_rules! with_runtime {
	($client: ident, $at: expr, $exec: expr) => {{
		let parent = $at.block_id();
		let header = Header {
			parent_hash: $client.block_hash_from_id(&parent)?
				.ok_or_else(|| ErrorKind::UnknownBlock(format!("{:?}", parent)))?,
			number: $client.block_number_from_id(&parent)?
				.ok_or_else(|| ErrorKind::UnknownBlock(format!("{:?}", parent)))? + 1,
			state_root: Default::default(),
			extrinsics_root: Default::default(),
			digest: Default::default(),
		};

		$client.state_at(&parent).map_err(Error::from).and_then(|state| {
			let mut changes = Default::default();
			let mut ext = state_machine::Ext::new(&mut changes, &state);

			::substrate_executor::with_native_environment(&mut ext, || {
				::runtime::Executive::initialise_block(&header);
				($exec)()
			}).map_err(Into::into)
		})
	}}
}

impl<B: LocalBackend<Block>> BlockBuilder for ClientBlockBuilder<B, LocalCallExecutor<B, NativeExecutor<LocalDispatch>>, Block>
	where ::client::error::Error: From<<<B as Backend<Block>>::State as state_machine::backend::Backend>::Error>
{
	fn push_extrinsic(&mut self, extrinsic: UncheckedExtrinsic) -> Result<()> {
		self.push(extrinsic).map_err(Into::into)
	}

	/// Bake the block with provided extrinsics.
	fn bake(self) -> Result<Block> {
		ClientBlockBuilder::bake(self).map_err(Into::into)
	}
}

impl<B: LocalBackend<Block>> PolkadotApi for Client<B, LocalCallExecutor<B, NativeExecutor<LocalDispatch>>, Block>
	where ::client::error::Error: From<<<B as Backend<Block>>::State as state_machine::backend::Backend>::Error>
{
	type CheckedBlockId = CheckedId;
	type BlockBuilder = ClientBlockBuilder<B, LocalCallExecutor<B, NativeExecutor<LocalDispatch>>, Block>;

	fn check_id(&self, id: BlockId) -> Result<CheckedId> {
		// bail if the code is not the same as the natively linked.
		if self.code_at(&id.into())? != LocalDispatch::native_equivalent() {
			bail!("This node is out of date. Block authoring may not work correctly. Bailing.")
		}

		Ok(CheckedId(id))
	}

	fn session_keys(&self, at: &CheckedId) -> Result<Vec<SessionKey>> {
		with_runtime!(self, at, ::runtime::Consensus::authorities)
	}

	fn validators(&self, at: &CheckedId) -> Result<Vec<AccountId>> {
		with_runtime!(self, at, ::runtime::Session::validators)
	}

	fn random_seed(&self, at: &CheckedId) -> Result<Hash> {
		with_runtime!(self, at, ::runtime::System::random_seed)
	}

	fn duty_roster(&self, at: &CheckedId) -> Result<DutyRoster> {
		with_runtime!(self, at, ::runtime::Parachains::calculate_duty_roster)
	}

	fn timestamp(&self, at: &CheckedId) -> Result<Timestamp> {
		with_runtime!(self, at, ::runtime::Timestamp::now)
	}

	fn evaluate_block(&self, at: &CheckedId, block: Block) -> Result<bool> {
		use substrate_executor::error::ErrorKind as ExecErrorKind;
		use codec::Slicable;
		use runtime::Block as RuntimeBlock;

		let encoded = block.encode();
		let runtime_block = match RuntimeBlock::decode(&mut &encoded[..]) {
			Some(x) => x,
			None => return Ok(false),
		};

		let res = with_runtime!(self, at, || ::runtime::Executive::execute_block(runtime_block));
		match res {
			Ok(()) => Ok(true),
			Err(err) => match err.kind() {
				&ErrorKind::Executor(ExecErrorKind::Runtime) => Ok(false),
				_ => Err(err)
			}
		}
	}

	fn index(&self, at: &CheckedId, account: AccountId) -> Result<Index> {
		with_runtime!(self, at, || ::runtime::System::account_index(account))
	}

	fn active_parachains(&self, at: &CheckedId) -> Result<Vec<ParaId>> {
		with_runtime!(self, at, ::runtime::Parachains::active_parachains)
	}

	fn parachain_code(&self, at: &CheckedId, parachain: ParaId) -> Result<Option<Vec<u8>>> {
		with_runtime!(self, at, || ::runtime::Parachains::parachain_code(parachain))
	}

	fn parachain_head(&self, at: &CheckedId, parachain: ParaId) -> Result<Option<Vec<u8>>> {
		with_runtime!(self, at, || ::runtime::Parachains::parachain_head(parachain))
	}

	fn build_block(&self, at: &CheckedId, timestamp: Timestamp, new_heads: Vec<CandidateReceipt>) -> Result<Self::BlockBuilder> {
		let mut block_builder = self.new_block_at(at.block_id())?;
		for inherent in self.inherent_extrinsics(at, timestamp, new_heads)? {
			block_builder.push(inherent)?;
		}

		Ok(block_builder)
	}

	fn inherent_extrinsics(&self, at: &Self::CheckedBlockId, timestamp: Timestamp, new_heads: Vec<CandidateReceipt>) -> Result<Vec<UncheckedExtrinsic>> {
		use codec::Slicable;

		with_runtime!(self, at, || {
			let extrinsics = ::runtime::inherent_extrinsics(timestamp, new_heads);
			extrinsics.into_iter()
				.map(|x| x.encode()) // get encoded representation
				.map(|x| Slicable::decode(&mut &x[..])) // get byte-vec equivalent to extrinsic
				.map(|x| x.expect("UncheckedExtrinsic has encoded representation equivalent to Vec<u8>; qed"))
				.collect()
		})
	}
}

impl<B: LocalBackend<Block>> LocalPolkadotApi for Client<B, LocalCallExecutor<B, NativeExecutor<LocalDispatch>>, Block>
	where ::client::error::Error: From<<<B as Backend<Block>>::State as state_machine::backend::Backend>::Error>
{}

#[cfg(test)]
mod tests {
	use super::*;
	use keyring::Keyring;
	use client::{self, LocalCallExecutor};
	use client::in_mem::Backend as InMemory;
	use substrate_executor::NativeExecutionDispatch;
	use runtime::{GenesisConfig, ConsensusConfig, SessionConfig, BuildExternalities};

	fn validators() -> Vec<AccountId> {
		vec![
			Keyring::One.to_raw_public().into(),
			Keyring::Two.to_raw_public().into(),
		]
	}

	fn session_keys() -> Vec<SessionKey> {
		vec![
			Keyring::One.to_raw_public(),
			Keyring::Two.to_raw_public(),
		]
	}

	fn client() -> Client<InMemory<Block>, LocalCallExecutor<InMemory<Block>, NativeExecutor<LocalDispatch>>, Block> {
		struct GenesisBuilder;

		impl client::GenesisBuilder<Block> for GenesisBuilder {
			fn build(self) -> (Header, Vec<(Vec<u8>, Vec<u8>)>) {
				let genesis_config = GenesisConfig {
					consensus: Some(ConsensusConfig {
						code: LocalDispatch::native_equivalent().to_vec(),
						authorities: session_keys(),
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
				let block = ::client::genesis::construct_genesis_block::<Block>(&storage);
				(block.header, storage.into_iter().collect())
			}
		}

		::client::new_in_mem(LocalDispatch::new(), GenesisBuilder).unwrap()
	}

	#[test]
	fn gets_session_and_validator_keys() {
		let client = client();
		let id = client.check_id(BlockId::number(0)).unwrap();
		assert_eq!(client.session_keys(&id).unwrap(), session_keys());
		assert_eq!(client.validators(&id).unwrap(), validators());
	}

	#[test]
	fn build_block_implicit_succeeds() {
		let client = client();

		let id = client.check_id(BlockId::number(0)).unwrap();
		let block_builder = client.build_block(&id, 1_000_000, Vec::new()).unwrap();
		let block = block_builder.bake().unwrap();

		assert_eq!(block.header.number, 1);
		assert!(block.header.extrinsics_root != Default::default());
	}

	#[test]
	fn build_block_with_inherent_succeeds() {
		let client = client();

		let id = client.check_id(BlockId::number(0)).unwrap();
		let inherent = client.inherent_extrinsics(&id, 1_000_000, Vec::new()).unwrap();

		let mut block_builder = client.new_block_at(id.block_id()).unwrap();
		for extrinsic in inherent {
			block_builder.push(extrinsic).unwrap();
		}

		let block = block_builder.bake().unwrap();

		assert_eq!(block.header.number, 1);
		assert!(block.header.extrinsics_root != Default::default());
	}

	#[test]
	fn fails_to_check_id_for_unknown_block() {
		assert!(client().check_id(BlockId::number(100)).is_err());
	}

	#[test]
	fn gets_random_seed_with_genesis() {
		let client = client();

		let id = client.check_id(BlockId::number(0)).unwrap();
		assert!(client.random_seed(&id).is_ok());
	}
}
