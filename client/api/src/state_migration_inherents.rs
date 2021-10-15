// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Inherent extrinsics used to indicate the share of state migration a block should handle.
//!
//! Providing the inherent is done by runing the migration once.
//! This allows that the over threshold state query is not included in the block processing.
//! This is relevant to avoid touching a big value when going over one of the thresholds.

use std::result::Result;

use crate::ExecutorProvider;
use codec::{Compact, Decode};
use sp_inherents::{InherentData, InherentIdentifier};
use sp_runtime::traits::Block as BlockT;
use sp_state_machine::ExecutionStrategy;

pub use sp_inherents::Error;

/// The identifier for the state migration.
pub const INHERENT_IDENTIFIER: InherentIdentifier = *b"mig_s0-1"; // TODO get this from pallet

/// Provider for inherent data, already contains input.
pub struct InherentDataProvider {
	number_items: u64,
}

#[async_trait::async_trait]
impl sp_inherents::InherentDataProvider for InherentDataProvider {
	fn provide_inherent_data(&self, inherent_data: &mut InherentData) -> Result<(), Error> {
		if self.number_items > 0 {
			inherent_data.put_data(INHERENT_IDENTIFIER, &Compact(self.number_items))
		} else {
			Ok(())
		}
	}

	async fn try_handle_error(
		&self,
		_: &InherentIdentifier,
		_: &[u8],
	) -> Option<Result<(), Error>> {
		None
	}
}

/// Create a new inherent migration provider instance for a given parent block hash.
/// This is running the migration for the block once and got a non negligeable
/// associated cost.
pub fn new_migration_provider<B, C>(
	client: &C,
	parent: &B::Hash,
) -> Result<InherentDataProvider, Error>
where
	B: BlockT,
	C: ExecutorProvider<B>,
{
	use crate::call_executor::CallExecutor;

	let id = sp_runtime::generic::BlockId::Hash(parent.clone());
	let executor = client.executor();
	let fn_call = "CalcPayload_calculate_pending_migration_size";
	let result = match executor.call(&id, fn_call, &[], ExecutionStrategy::NativeElseWasm, None) {
		Ok(result) => result,
		Err(e) => {
			log::debug!("Inherent provider without runtime function: {:?}", e);
			return Ok(InherentDataProvider { number_items: 0 })
		},
	};

	let number_items =
		u64::decode(&mut result.as_slice()).map_err(|_decode_err| Error::FatalErrorReported)?;

	Ok(InherentDataProvider { number_items })
}
