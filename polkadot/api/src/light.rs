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
use codec::Decode;
use primitives::{
	AccountId, Block, BlockId, Hash, Index, InherentData,
	SessionKey, Timestamp, UncheckedExtrinsic,
};
use runtime::Address;
use primitives::parachain::{DutyRoster, Id as ParaId};
use {PolkadotApi, BlockBuilder, RemotePolkadotApi, Result, ErrorKind};
use substrate_primitives::{KeccakHasher, RlpCodec};

/// Light block builder. TODO: make this work (efficiently)
#[derive(Clone, Copy)]
pub struct LightBlockBuilder;

impl BlockBuilder for LightBlockBuilder {
	fn push_extrinsic(&mut self, _xt: UncheckedExtrinsic) -> Result<()> {
		Err(ErrorKind::UnknownRuntime.into())
	}

	fn bake(self) -> Result<Block> {
		Err(ErrorKind::UnknownRuntime.into())
	}
}

/// Remote polkadot API implementation.
pub struct RemotePolkadotApiWrapper<B: Backend<Block, KeccakHasher, RlpCodec>, E: CallExecutor<Block, KeccakHasher, RlpCodec>>(pub Arc<Client<B, E, Block>>);

impl<B: Backend<Block, KeccakHasher, RlpCodec>, E: CallExecutor<Block, KeccakHasher, RlpCodec>> PolkadotApi for RemotePolkadotApiWrapper<B, E> {
	type BlockBuilder = LightBlockBuilder;

	fn session_keys(&self, at: &BlockId) -> Result<Vec<SessionKey>> {
		self.0.executor().call(at, "authorities", &[])
			.and_then(|r| Vec::<SessionKey>::decode(&mut &r.return_data[..])
				.ok_or("error decoding session keys".into()))
			.map_err(Into::into)
	}

	fn validators(&self, _at: &BlockId) -> Result<Vec<AccountId>> {
		Err(ErrorKind::UnknownRuntime.into())
	}

	fn random_seed(&self, _at: &BlockId) -> Result<Hash> {
		Err(ErrorKind::UnknownRuntime.into())
	}

	fn duty_roster(&self, _at: &BlockId) -> Result<DutyRoster> {
		Err(ErrorKind::UnknownRuntime.into())
	}

	fn timestamp(&self, _at: &BlockId) -> Result<Timestamp> {
		Err(ErrorKind::UnknownRuntime.into())
	}

	fn evaluate_block(&self, _at: &BlockId, _block: Block) -> Result<bool> {
		Err(ErrorKind::UnknownRuntime.into())
	}

	fn index(&self, _at: &BlockId, _account: AccountId) -> Result<Index> {
		Err(ErrorKind::UnknownRuntime.into())
	}

	fn lookup(&self, _at: &BlockId, _address: Address) -> Result<Option<AccountId>> {
		Err(ErrorKind::UnknownRuntime.into())
	}

	fn active_parachains(&self, _at: &BlockId) -> Result<Vec<ParaId>> {
		Err(ErrorKind::UnknownRuntime.into())
	}

	fn parachain_code(&self, _at: &BlockId, _parachain: ParaId) -> Result<Option<Vec<u8>>> {
		Err(ErrorKind::UnknownRuntime.into())
	}

	fn parachain_head(&self, _at: &BlockId, _parachain: ParaId) -> Result<Option<Vec<u8>>> {
		Err(ErrorKind::UnknownRuntime.into())
	}

	fn build_block(&self, _at: &BlockId, _inherent: InherentData) -> Result<Self::BlockBuilder> {
		Err(ErrorKind::UnknownRuntime.into())
	}

	fn inherent_extrinsics(&self, _at: &BlockId, _inherent: InherentData) -> Result<Vec<Vec<u8>>> {
		Err(ErrorKind::UnknownRuntime.into())
	}
}

impl<B: RemoteBackend<Block, KeccakHasher, RlpCodec>, E: CallExecutor<Block, KeccakHasher, RlpCodec>> RemotePolkadotApi for RemotePolkadotApiWrapper<B, E> {}
