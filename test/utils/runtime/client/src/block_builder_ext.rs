// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Block Builder extensions for tests.

use runtime;
use sr_primitives::traits::ProvideRuntimeApi;

use block_builder::BlockBuilderApi;

/// Extension trait for test block builder.
pub trait BlockBuilderExt {
	/// Add transfer extrinsic to the block.
	fn push_transfer(&mut self, transfer: runtime::Transfer) -> Result<(), sp_blockchain::Error>;
	/// Add storage change extrinsic to the block.
	fn push_storage_change(
		&mut self,
		key: Vec<u8>,
		value: Option<Vec<u8>>,
	) -> Result<(), sp_blockchain::Error>;
}

impl<'a, A> BlockBuilderExt for block_builder::BlockBuilder<'a, runtime::Block, A> where
	A: ProvideRuntimeApi + 'a,
	A::Api: BlockBuilderApi<runtime::Block, Error = sp_blockchain::Error>,
{
	fn push_transfer(&mut self, transfer: runtime::Transfer) -> Result<(), sp_blockchain::Error> {
		self.push(transfer.into_signed_tx())
	}

	fn push_storage_change(
		&mut self,
		key: Vec<u8>,
		value: Option<Vec<u8>>,
	) -> Result<(), sp_blockchain::Error> {
		self.push(runtime::Extrinsic::StorageChange(key, value))
	}
}
