// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

use crate::error::Error;
use log::info;
use sp_runtime::traits::{Block as BlockT, NumberFor, Zero};
use sc_client_api::{Backend, UsageProvider};
use std::sync::Arc;

/// Performs a revert of `blocks` blocks.
pub fn revert_chain<B, BA, C>(
	client: Arc<C>,
	backend: Arc<BA>,
	blocks: NumberFor<B>
) -> Result<(), Error>
where
	B: BlockT,
	C: UsageProvider<B>,
	BA: Backend<B>,
{
	let reverted = backend.revert(blocks, false)?;
	let info = client.usage_info().chain;

	if reverted.is_zero() {
		info!("There aren't any non-finalized blocks to revert.");
	} else {
		info!("Reverted {} blocks. Best: #{} ({})", reverted, info.best_number, info.best_hash);
	}
	Ok(())
}
