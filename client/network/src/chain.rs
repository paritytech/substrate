// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Blockchain access trait

use sc_client_api::{BlockBackend, ProofProvider};
pub use sc_client_api::{StorageData, StorageKey};
pub use sc_consensus::ImportedState;
use sp_blockchain::{Error, HeaderBackend, HeaderMetadata};
use sp_runtime::traits::{Block as BlockT, BlockIdTo};

/// Local client abstraction for the network.
pub trait Client<Block: BlockT>:
	HeaderBackend<Block>
	+ ProofProvider<Block>
	+ BlockIdTo<Block, Error = Error>
	+ BlockBackend<Block>
	+ HeaderMetadata<Block, Error = Error>
	+ Send
	+ Sync
{
}

impl<Block: BlockT, T> Client<Block> for T where
	T: HeaderBackend<Block>
		+ ProofProvider<Block>
		+ BlockIdTo<Block, Error = Error>
		+ BlockBackend<Block>
		+ HeaderMetadata<Block, Error = Error>
		+ Send
		+ Sync
{
}
