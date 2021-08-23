// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use sp_consensus::Proposal;
use sp_runtime::traits::Block as BlockT;

use crate::{PowAlgorithm, Seal};

/// Mining metadata. This is the information needed to start an actual mining loop.
#[derive(Clone, Eq, PartialEq)]
pub struct MiningMetadata<H, D> {
	/// Currently known best hash which the pre-hash is built on.
	pub best_hash: H,
	/// Mining pre-hash.
	pub pre_hash: H,
	/// Pre-runtime digest item.
	pub pre_runtime: Option<Vec<u8>>,
	/// Mining target difficulty.
	pub difficulty: D,
}

#[derive(Clone)]
pub struct MiningData<H, D> {
	pub metadata: MiningMetadata<H, D>,
	/// sink to send the seal back to the authorship task
	pub sender: tokio::sync::mpsc::Sender<Seal>,
}

/// A build of mining, containing the metadata and the block proposal.
pub struct MiningBuild<B: BlockT, A: PowAlgorithm<B>, C: sp_api::ProvideRuntimeApi<B>, P> {
	/// Mining metadata.
	pub metadata: MiningMetadata<B::Hash, A::Difficulty>,
	/// Mining proposal.
	pub proposal: Proposal<B, sp_api::TransactionFor<C, B>, P>,
}
