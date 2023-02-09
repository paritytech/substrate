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

use crate::error::Error;
use codec::Encode;
use sc_client_api::{BlockBackend, HeaderBackend};
use sc_consensus::import_queue::ImportQueue;
use sp_runtime::{generic::BlockId, traits::Block as BlockT};

use crate::chain_ops::import_blocks;
use std::sync::Arc;

/// Re-validate known block.
pub async fn check_block<B, IQ, C>(
	client: Arc<C>,
	import_queue: IQ,
	block_id: BlockId<B>,
) -> Result<(), Error>
where
	C: BlockBackend<B> + HeaderBackend<B> + Send + Sync + 'static,
	B: BlockT + for<'de> serde::Deserialize<'de>,
	IQ: ImportQueue<B> + 'static,
{
	let maybe_block = client
		.block_hash_from_id(&block_id)?
		.map(|hash| client.block(hash))
		.transpose()?
		.flatten();
	match maybe_block {
		Some(block) => {
			let mut buf = Vec::new();
			1u64.encode_to(&mut buf);
			block.encode_to(&mut buf);
			let reader = std::io::Cursor::new(buf);
			import_blocks(client, import_queue, reader, true, true).await
		},
		None => Err("Unknown block")?,
	}
}
