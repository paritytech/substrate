// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Substrate light Client

use futures::sync::mpsc;
use parking_lot::Mutex;
use full_client::{BlockchainEvents, BlockchainEventStream, ChainHead, ChainData,
	StateData, ContractCaller, CallResult, BlockImportNotification};
use full_client::error;
use primitives::block;
use primitives::block::Id as BlockId;
use primitives::storage::{StorageKey, StorageData};

/// Polkadot light client
#[derive(Default)]
pub struct LightClient {
	import_notification_sinks: Mutex<Vec<mpsc::UnboundedSender<BlockImportNotification>>>,
}

impl BlockchainEvents for LightClient {
	fn import_notification_stream(&self) -> BlockchainEventStream {
		let (sink, stream) = mpsc::unbounded();
		self.import_notification_sinks.lock().push(sink);
		stream
	}
}

impl ChainHead for LightClient {
	fn best_block_header(&self) -> error::Result<block::Header> {
		Err(error::ErrorKind::NotImplemented.into())
	}

	fn best_block_hash(&self) -> error::Result<block::HeaderHash> {
		Err(error::ErrorKind::NotImplemented.into())
	}
}

impl ChainData for LightClient {
	fn header(&self, _id: &BlockId) -> error::Result<Option<block::Header>> {
		Err(error::ErrorKind::NotImplemented.into())
	}
}

impl StateData for LightClient {
	fn code_at(&self, _id: &BlockId) -> error::Result<Vec<u8>> {
		Err(error::ErrorKind::NotImplemented.into())
	}

	fn storage(&self, _id: &BlockId, _key: &StorageKey) -> error::Result<StorageData> {
		Err(error::ErrorKind::NotImplemented.into())
	}
}

impl ContractCaller for LightClient {
	fn call(&self, _id: &BlockId, _method: &str, _call_data: &[u8]) -> Result<CallResult, error::Error> {
		Err(error::ErrorKind::NotImplemented.into())
	}
}

/// Create an instance of in-memory client.
pub fn new_in_mem() -> error::Result<LightClient> {
	Ok(Default::default())
}
