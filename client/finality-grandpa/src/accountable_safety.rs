// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

use futures::StreamExt;
use std::sync::Arc;

use sp_api::ProvideRuntimeApi;
use sp_finality_grandpa::GrandpaApi;
use sp_runtime::{generic::BlockId, traits::Block as BlockT};

use sc_client_api::BlockchainEvents;

/// Start the GRANDPA accountable safety worker
pub async fn run_grandpa_accountable_safety_worker<B, C>(client: Arc<C>)
where
	B: BlockT,
	C: BlockchainEvents<B>,
{
	let worker = AccountableSafetyWorker {
		client: client.clone(),
	};

	run_accountable_safety_protocol(client, worker).await
}

/// Run the accountable safety worker, which has as primary responsibility to detect inconsistent
/// finality, and reply to queries.
async fn run_accountable_safety_protocol<B, C>(client: Arc<C>, _worker: AccountableSafetyWorker<C>)
where
	B: BlockT,
	C: BlockchainEvents<B>,
{
	loop {
		if let Some(_block) = client.import_notification_stream().next().await {
			// The accountable safety worker looks at incoming blocks
		}
	}
}

#[allow(unused)]
struct AccountableSafetyWorker<C> {
	client: Arc<C>,
}

impl<C> AccountableSafetyWorker<C> {
	/// Scan imported blocks for inconsisent finality, where two finalized blocks are neither
	/// ancestor or descendent of each other.
	// This might mean inspecting incoming commits before they are imported.
	#[allow(unused)]
	async fn scan_for_inconsisent_finality(&mut self) {
		todo!();
	}

	/// If the accountable safety protocol on-chain puts out queries, and we are among the
	/// recipients, we need to submit our reply.
	#[allow(unused)]
	async fn respond_to_queries<B>(&mut self, block_id: BlockId<B>)
	where
		B: BlockT,
		C: ProvideRuntimeApi<B>,
		C::Api: GrandpaApi<B>,
	{
		if let Ok(Some(accountable_safety)) = self
			.client
			.runtime_api()
			.accountable_safety_state(&block_id)
		{
			// Respond if asked to
			self.client
				.runtime_api()
				.submit_accountable_safety_response_extrinsic(&block_id);
		}

		todo!();
	}
}
