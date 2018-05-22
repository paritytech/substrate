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
use client::{self, Client, LocalCallExecutor};
use polkadot_executor::Executor as LocalDispatch;
use substrate_executor::{NativeExecutionDispatch, NativeExecutor};
use state_machine::{self, OverlayedChanges};
use primitives::{AccountId, BlockId, Hash, Index, SessionKey, Timestamp};
use primitives::parachain::DutyRoster;
use runtime::{self, Block, Header, UncheckedExtrinsic, Extrinsic, Call, TimestampCall};
use {CheckedBlockId, BlockBuilder, PolkadotApi, LocalPolkadotApi, ErrorKind, Error, Result};

/// A checked block ID used for the substrate-client implementation of CheckedBlockId;
#[derive(Debug, Clone, Copy)]
pub struct CheckedId(pub BlockId);

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
			parent_hash: $client.block_hash_from_id(parent)?.ok_or(ErrorKind::UnknownBlock(*parent))?,
			number: $client.block_number_from_id(parent)?.ok_or(ErrorKind::UnknownBlock(*parent))? + 1,
			state_root: Default::default(),
			extrinsics_root: Default::default(),
			digest: Default::default(),
		};

		$client.state_at(parent).map_err(Error::from).and_then(|state| {
			let mut changes = Default::default();
			let mut ext = state_machine::Ext::new(&mut changes, &state);

			::substrate_executor::with_native_environment(&mut ext, || {
				::runtime::Executive::initialise_block(&header);
				($exec)()
			}).map_err(Into::into)
		})
	}}
}

/// A polkadot block builder.
#[derive(Debug, Clone)]
pub struct ClientBlockBuilder<S> {
	parent: BlockId,
	changes: OverlayedChanges,
	state: S,
	header: Header,
	timestamp: Timestamp,
	extrinsics: Vec<UncheckedExtrinsic>,
}

impl<S: state_machine::Backend> ClientBlockBuilder<S>
	where S::Error: Into<client::error::Error>
{
	// initialises a block ready to allow extrinsics to be applied.
	fn initialise_block(&mut self) -> Result<()> {
		let result = {
			let mut ext = state_machine::Ext::new(&mut self.changes, &self.state);
			let h = self.header.clone();

			::substrate_executor::with_native_environment(
				&mut ext,
				|| runtime::Executive::initialise_block(&h),
			).map_err(Into::into)
		};

		match result {
			Ok(_) => {
				self.changes.commit_prospective();
				Ok(())
			}
			Err(e) => {
				self.changes.discard_prospective();
				Err(e)
			}
		}
	}

	// executes a extrinsic, inherent or otherwise, without appending to the list.
	fn apply_extrinsic(&mut self, extrinsic: UncheckedExtrinsic) -> Result<()> {
		let result = {
			let mut ext = state_machine::Ext::new(&mut self.changes, &self.state);

			::substrate_executor::with_native_environment(
				&mut ext,
				move || runtime::Executive::apply_extrinsic(extrinsic),
			).map_err(Into::into)
		};

		match result {
			Ok(_) => {
				self.changes.commit_prospective();
				Ok(())
			}
			Err(e) => {
				self.changes.discard_prospective();
				Err(e)
			}
		}
	}
}

impl<S: state_machine::Backend> BlockBuilder for ClientBlockBuilder<S>
	where S::Error: Into<client::error::Error>
{
	fn push_extrinsic(&mut self, extrinsic: UncheckedExtrinsic) -> Result<()> {
		// Check that this is not an "inherent" extrinsic.
		if extrinsic.signature == Default::default() {
			bail!(ErrorKind::PushedInherentTransaction(extrinsic));
		} else {
			self.apply_extrinsic(extrinsic.clone())?;
			self.extrinsics.push(extrinsic);
			Ok(())
		}
	}

	fn bake(mut self) -> Block {
		let mut ext = state_machine::Ext::new(&mut self.changes, &self.state);

		let final_header = ::substrate_executor::with_native_environment(
			&mut ext,
			move || runtime::Executive::finalise_block()
		).expect("all inherent extrinsics pushed; all other extrinsics executed correctly; qed");
		Block {
			header: final_header,
			extrinsics: self.extrinsics,
		}
	}
}

impl<B: LocalBackend> PolkadotApi for Client<B, LocalCallExecutor<B, NativeExecutor<LocalDispatch>>>
	where ::client::error::Error: From<<<B as Backend>::State as state_machine::backend::Backend>::Error>
{
	type CheckedBlockId = CheckedId;
	type BlockBuilder = ClientBlockBuilder<B::State>;

	fn check_id(&self, id: BlockId) -> Result<CheckedId> {
		// bail if the code is not the same as the natively linked.
		if self.code_at(&id)? != LocalDispatch::native_equivalent() {
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

	fn evaluate_block(&self, at: &CheckedId, block: Block) -> Result<()> {
		with_runtime!(self, at, || ::runtime::Executive::execute_block(block))
	}

	fn index(&self, at: &CheckedId, account: AccountId) -> Result<Index> {
		with_runtime!(self, at, || ::runtime::System::account_index(account))
	}

	fn build_block(&self, parent: &CheckedId, timestamp: Timestamp) -> Result<Self::BlockBuilder> {
		let parent = parent.block_id();
		let header = Header {
			parent_hash: self.block_hash_from_id(parent)?.ok_or(ErrorKind::UnknownBlock(*parent))?,
			number: self.block_number_from_id(parent)?.ok_or(ErrorKind::UnknownBlock(*parent))? + 1,
			state_root: Default::default(),
			extrinsics_root: Default::default(),
			digest: Default::default(),
		};

		let extrinsics = vec![
			UncheckedExtrinsic {
				extrinsic: Extrinsic {
					signed: Default::default(),
					index: Default::default(),
					function: Call::Timestamp(TimestampCall::set(timestamp)),
				},
				signature: Default::default(),
			}
		];

		let mut builder = ClientBlockBuilder {
			parent: *parent,
			changes: OverlayedChanges::default(),
			state: self.state_at(parent)?,
			header,
			timestamp,
			extrinsics: extrinsics.clone(),
		};

		builder.initialise_block()?;

		for inherent in extrinsics {
			builder.apply_extrinsic(inherent)?;
		}

		Ok(builder)
	}
}

impl<B: LocalBackend> LocalPolkadotApi for Client<B, LocalCallExecutor<B, NativeExecutor<LocalDispatch>>>
	where ::client::error::Error: From<<<B as Backend>::State as state_machine::backend::Backend>::Error>
{}
