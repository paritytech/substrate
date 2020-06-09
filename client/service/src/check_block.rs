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

#![allow(unused_imports)]

use crate::error;
use crate::error::Error;
use sc_chain_spec::ChainSpec;
use log::{warn, info};
use futures::{future, prelude::*};
use sp_runtime::traits::{
	Block as BlockT, NumberFor, One, Zero, Header, SaturatedConversion
};
use sp_runtime::generic::{BlockId, SignedBlock};
use codec::{Decode, Encode, IoReader};
use crate::client::{Client, LocalCallExecutor};
use sp_consensus::{
	BlockOrigin,
	import_queue::{IncomingBlock, Link, BlockImportError, BlockImportResult, ImportQueue},
};
use crate::config::RpcMethods;
use sc_executor::{NativeExecutor, NativeExecutionDispatch};
use sc_client_api::client::BlockBackend;

use std::{io::{Read, Write, Seek}, pin::Pin};
use std::sync::Arc;
use crate::import_blocks::import_blocks;

pub fn check_block<B, BA, CE, RA, IQ>(
	client: Arc<Client<BA, CE, B, RA>>,
	import_queue: IQ,
	block_id: BlockId<B>
) -> Pin<Box<dyn Future<Output = Result<(), Error>> + Send>>
where
	B: BlockT + for<'de> serde::Deserialize<'de>,
	BA: sc_client_api::backend::Backend<B> + 'static,
	CE: sc_client_api::call_executor::CallExecutor<B> + Send + Sync + 'static,
	IQ: ImportQueue<B> + 'static,
	RA: Send + Sync + 'static,
{
	match client.block(&block_id) {
		Ok(Some(block)) => {
			let mut buf = Vec::new();
			1u64.encode_to(&mut buf);
			block.encode_to(&mut buf);
			let reader = std::io::Cursor::new(buf);
			import_blocks(client, import_queue, reader, true, true)
		}
		Ok(None) => Box::pin(future::err("Unknown block".into())),
		Err(e) => Box::pin(future::err(format!("Error reading block: {:?}", e).into())),
	}
}
