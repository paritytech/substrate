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

//! Block finalization utilities

use crate::rpc;
use sc_client_api::backend::{Backend as ClientBackend, Finalizer};
use sp_runtime::{generic::BlockId, traits::Block as BlockT, Justification};
use std::{marker::PhantomData, sync::Arc};

/// params for block finalization.
pub struct FinalizeBlockParams<B: BlockT, F, CB> {
	/// hash of the block
	pub hash: <B as BlockT>::Hash,
	/// sender to report errors/success to the rpc.
	pub sender: rpc::Sender<()>,
	/// finalization justification
	pub justification: Option<Justification>,
	/// Finalizer trait object.
	pub finalizer: Arc<F>,
	/// phantom type to pin the Backend type
	pub _phantom: PhantomData<CB>,
}

/// finalizes a block in the backend with the given params.
pub async fn finalize_block<B, F, CB>(params: FinalizeBlockParams<B, F, CB>)
where
	B: BlockT,
	F: Finalizer<B, CB>,
	CB: ClientBackend<B>,
{
	let FinalizeBlockParams { hash, mut sender, justification, finalizer, .. } = params;

	match finalizer.finalize_block(BlockId::Hash(hash), justification, true) {
		Err(e) => {
			log::warn!("Failed to finalize block {:?}", e);
			rpc::send_result(&mut sender, Err(e.into()))
		},
		Ok(()) => {
			log::info!("✅ Successfully finalized block: {}", hash);
			rpc::send_result(&mut sender, Ok(()))
		},
	}
}
