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
use crate::client::Client;

use std::sync::Arc;

/// Performs a revert of `blocks` blocks.
pub fn revert_chain<B, BA, CE, RA>(
	client: Arc<Client<BA, CE, B, RA>>,
	blocks: NumberFor<B>
) -> Result<(), Error>
where
	B: BlockT,
	BA: sc_client_api::backend::Backend<B> + 'static,
	CE: sc_client_api::call_executor::CallExecutor<B> + Send + Sync + 'static,
	RA: Send + Sync + 'static,
{
	let reverted = client.revert(blocks)?;
	let info = client.chain_info();

	if reverted.is_zero() {
		info!("There aren't any non-finalized blocks to revert.");
	} else {
		info!("Reverted {} blocks. Best: #{} ({})", reverted, info.best_number, info.best_hash);
	}
	Ok(())
}
