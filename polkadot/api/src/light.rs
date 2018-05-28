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

//! Strongly typed API for light Polkadot client.

use std::sync::Arc;
use client::backend::{Backend, RemoteBackend};
use client::{Client, CallExecutor};
use codec::Slicable;
use state_machine;
use primitives::{AccountId, BlockId, Hash, Index, SessionKey, Timestamp};
use primitives::parachain::{DutyRoster, CandidateReceipt, Id as ParaId};
use runtime::{Block, UncheckedExtrinsic};
use full::CheckedId;
use {PolkadotApi, RemotePolkadotApi, BlockBuilder, CheckedBlockId, Result, ErrorKind};

/// Remote polkadot API implementation.
pub struct RemotePolkadotApiWrapper<B: Backend, E: CallExecutor>(pub Arc<Client<B, E>>);

/// Block builder for light client.
pub struct LightBlockBuilder;

impl<B: Backend, E: CallExecutor> PolkadotApi for RemotePolkadotApiWrapper<B, E>
	where ::client::error::Error: From<<<B as Backend>::State as state_machine::backend::Backend>::Error>
{
	type CheckedBlockId = CheckedId;
	type BlockBuilder = LightBlockBuilder;

	fn check_id(&self, id: BlockId) -> Result<CheckedId> {
		Ok(CheckedId(id))
	}

	fn session_keys(&self, at: &CheckedId) -> Result<Vec<SessionKey>> {
		self.0.executor().call(at.block_id(), "authorities", &[])
			.and_then(|r| Vec::<SessionKey>::decode(&mut &r.return_data[..])
				.ok_or("error decoding session keys".into()))
			.map_err(Into::into)
	}

	fn validators(&self, _at: &CheckedId) -> Result<Vec<AccountId>> {
		Err(ErrorKind::UnknownRuntime.into())
	}

	fn random_seed(&self, _at: &Self::CheckedBlockId) -> Result<Hash> {
		Err(ErrorKind::UnknownRuntime.into())
	}

	fn duty_roster(&self, _at: &CheckedId) -> Result<DutyRoster> {
		Err(ErrorKind::UnknownRuntime.into())
	}

	fn timestamp(&self, _at: &CheckedId) -> Result<Timestamp> {
		Err(ErrorKind::UnknownRuntime.into())
	}

	fn evaluate_block(&self, _at: &CheckedId, _block: Block) -> Result<bool> {
		Err(ErrorKind::UnknownRuntime.into())
	}

	fn index(&self, _at: &CheckedId, _account: AccountId) -> Result<Index> {
		Err(ErrorKind::UnknownRuntime.into())
	}

	fn active_parachains(&self, _at: &Self::CheckedBlockId) -> Result<Vec<ParaId>> {
		Err(ErrorKind::UnknownRuntime.into())
	}

	fn parachain_code(&self, _at: &Self::CheckedBlockId, _parachain: ParaId) -> Result<Option<Vec<u8>>> {
		Err(ErrorKind::UnknownRuntime.into())
	}

	fn parachain_head(&self, _at: &Self::CheckedBlockId, _parachain: ParaId) -> Result<Option<Vec<u8>>> {
		Err(ErrorKind::UnknownRuntime.into())
	}

	fn build_block(&self, _parent: &CheckedId, _timestamp: Timestamp, _parachains: Vec<CandidateReceipt>) -> Result<Self::BlockBuilder> {
		Err(ErrorKind::UnknownRuntime.into())
	}
}

impl<B: RemoteBackend, E: CallExecutor> RemotePolkadotApi for RemotePolkadotApiWrapper<B, E>
	where ::client::error::Error: From<<<B as Backend>::State as state_machine::backend::Backend>::Error>
{}

impl BlockBuilder for LightBlockBuilder {
	fn push_extrinsic(&mut self, _extrinsic: UncheckedExtrinsic) -> Result<()> {
		Err(ErrorKind::UnknownRuntime.into())
	}

	fn bake(self) -> Block {
		unimplemented!()
	}
}
