// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Uncles functionality for Substrate.

use sc_client_api::ProvideUncles;
use sp_runtime::{generic::BlockId, traits::Block as BlockT};

#[derive(Debug, thiserror::Error)]
pub enum Error<B: BlockT> {
	#[error("Could not retrieve the block hash for block id: {0:?}")]
	NoHashForBlockId(BlockId<B>),
}

/// Maximum uncles generations we may provide to the runtime.
const MAX_UNCLE_GENERATIONS: u32 = 8;

/// Create a new [`sp_authorship::InherentDataProvider`] at the given block.
pub fn create_uncles_inherent_data_provider<B, C>(
	client: &C,
	parent: B::Hash,
) -> Result<sp_authorship::InherentDataProvider<B::Header>, sc_client_api::blockchain::Error>
where
	B: BlockT,
	C: ProvideUncles<B>,
{
	let uncles = client.uncles(parent, MAX_UNCLE_GENERATIONS.into())?;

	Ok(sp_authorship::InherentDataProvider::new(uncles))
}
