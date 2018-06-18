// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Statement routing and consenuss table router implementation.

use polkadot_api::{PolkadotApi, LocalPolkadotApi};
use polkadot_consensus::{SharedTable, TableRouter, SignedStatement};
use polkadot_primitives::{Hash, BlockId, SessionKey};
use polkadot_primitives::parachain::{BlockData, Extrinsic, CandidateReceipt};

use futures::{future, prelude::*};
use tokio::runtime::TaskExecutor;

use std::sync::Arc;

use super::NetworkService;

/// Table routing implementation.
pub struct Router<P: PolkadotApi> {
	pub(crate) table: Arc<SharedTable>,
	pub(crate) network: Arc<NetworkService>,
	pub(crate) api: Arc<P>,
	pub(crate) task_executor: TaskExecutor,
	pub(crate) parent_hash: Option<P::CheckedBlockId>,
}


impl<P: PolkadotApi> Clone for Router<P> {
	fn clone(&self) -> Self {
		Router {
			table: self.table.clone(),
			network: self.network.clone(),
			api: self.api.clone(),
			task_executor: self.task_executor.clone(),
			parent_hash: self.parent_hash.clone(),
		}
	}
}

impl<P: LocalPolkadotApi + Send + Sync + 'static> Router<P> where P::CheckedBlockId: Send {
	pub(crate) fn import_statement(&self, statement: SignedStatement) {
		let api = self.api.clone();
		let parent_hash = self.parent_hash.clone();

		let validate_collation = move |collation| -> Option<bool> {
			let checked = parent_hash.clone()?;

			match ::polkadot_consensus::validate_collation(&*api, &checked, &collation) {
				Ok(()) => Some(true),
				Err(e) => {
					debug!(target: "p_net", "Encountered bad collation: {}", e);
					Some(false)
				}
			}
		};

		let producer = self.table.import_remote_statement(
			self,
			statement,
			validate_collation,
		);

		if !producer.is_blank() {
			let table = self.table.clone();
			self.task_executor.spawn(producer.map(move |produced| {
				// TODO: ensure availability of block/extrinsic
				// and propagate these statements.
				if let Some(validity) = produced.validity {
					table.sign_and_import(validity);
				}

				if let Some(availability) = produced.availability {
					table.sign_and_import(availability);
				}
			}))
		}
	}
}

impl<P: LocalPolkadotApi + Send> TableRouter for Router<P> where P::CheckedBlockId: Send {
	type Error = ();
	type FetchCandidate = future::Empty<BlockData, Self::Error>;
	type FetchExtrinsic = Result<Extrinsic, Self::Error>;

	fn local_candidate_data(&self, _hash: Hash, _block_data: BlockData, _extrinsic: Extrinsic) {
		// give to network to make available and multicast
	}

	fn fetch_block_data(&self, _candidate: &CandidateReceipt) -> Self::FetchCandidate {
		future::empty()
	}

	fn fetch_extrinsic_data(&self, _candidate: &CandidateReceipt) -> Self::FetchExtrinsic {
		Ok(Extrinsic)
	}
}
