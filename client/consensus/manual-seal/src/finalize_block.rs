// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Block finalization utilities

use crate::rpc;
use sp_runtime::{
	Justification,
	traits::Block as BlockT,
	generic::BlockId,
};
use std::sync::Arc;
use sc_client_api::backend::{Backend as ClientBackend, Finalizer};
use std::marker::PhantomData;

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
	let FinalizeBlockParams {
		hash,
		mut sender,
		justification,
		finalizer,
		..
	} = params;

	match finalizer.finalize_block(BlockId::Hash(hash), justification, true) {
		Err(e) => {
			log::warn!("Failed to finalize block {:?}", e);
			rpc::send_result(&mut sender, Err(e.into()))
		}
		Ok(()) => {
			log::info!("✅ Successfully finalized block: {}", hash);
			rpc::send_result(&mut sender, Ok(()))
		}
	}
}
