// Copyright 2018 Parity Technologies (UK) Ltd.
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

/// Traits for interfacing with the runtime from the client.

use client::Client;
use error;
use backend;
use call_executor::CallExecutor;
use blockchain::HeaderBackend;
pub use sr_api::*;
pub use sr_api::core::{CallApiAt, Core, ConstructRuntimeApi};
use sr_api;
use runtime_primitives::traits::{Block as BlockT, self, Header as HeaderT, As, ProvideRuntimeApi};
use primitives::Blake2Hasher;
use state_machine::OverlayedChanges;

use std::{ops::Deref, ptr::NonNull, mem};

pub struct ApiWithOverlay<B, E, Block: BlockT, RA> {
	overlay: OverlayedChanges,
	client: NonNull<Client<B, E, Block, RA>>,
	api: RA,
	initialised_block: Option<BlockId<Block>>,
	commit_on_success: bool,
}

impl<B, E, Block, RA> ApiWithOverlay<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone,
	Block: BlockT,
	RA: Core<Block>,
{
	pub(crate) fn new(client: &Client<B, E, Block, RA>) -> Self {
		let api = unsafe { client.runtime_api().into_inner() };
		let client = unsafe { NonNull::new_unchecked(mem::transmute(client)) };
		ApiWithOverlay {
			overlay: Default::default(),
			client,
			api,
			initialised_block: None,
			commit_on_success: true,
		}
	}
}

impl<B, E, Block, RA> traits::ApiWithOverlay for ApiWithOverlay<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone,
	Block: BlockT,
	RA: Core<Block>
{
	type Api = RA;

	fn map_api_result<F: FnOnce(&Self::Api) -> Result<R, Error>, R, Error>(&mut self, map_call: F) -> Result<R, Error> {
		self.commit_on_success = false;
		let res = map_call(self);
		self.commit_on_success = true;

		if res.is_err() {
			self.overlay.discard_prospective();
		} else {
			self.overlay.commit_prospective();
		}

		res
	}
}

impl<B, E, Block, RA> Deref for ApiWithOverlay<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone,
	Block: BlockT,
	RA: Core<Block>
{
	type Target = RA;

	fn deref(&self) -> &Self::Target {
		self.api.replace_call(self);
		&self.api
	}
}

impl<B, E, Block, RA> CallApiAt<Block> for ApiWithOverlay<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone,
	Block: BlockT,
	RA: Core<Block>,
{
	fn call_api_at(
		&mut self,
		at: &BlockId<Block>,
		function: &'static str,
		args: Vec<u8>,
	) -> sr_api::error::Result<Vec<u8>> {
		//TODO: Find a better way to prevent double block initialization
		if function != "initialise_block" && self.initialised_block.map(|id| id != *at).unwrap_or(true) {
			let parent = at;
			let header = <<Block as BlockT>::Header as HeaderT>::new(
				unsafe { self.client.as_ref().block_number_from_id(parent)
					.and_then(|v|
						v.ok_or_else(|| error::ErrorKind::UnknownBlock(format!("{:?}", parent)).into())
					).map_err(|e| sr_api::error::ErrorKind::GenericError(Box::new(e)))? }
				+ As::sa(1),
				Default::default(),
				Default::default(),
				unsafe { self.client.as_ref().block_hash_from_id(&parent)
					.and_then(|v|
						v.ok_or_else(|| error::ErrorKind::UnknownBlock(format!("{:?}", parent)).into())
					).map_err(|e| sr_api::error::ErrorKind::GenericError(Box::new(e)))? },
				Default::default()
			);
			self.api.initialise_block(at, &header)?;
			self.initialised_block = Some(*at);
		}
		let res = unsafe { self.client.as_ref().call_at_state(at, function, args, &mut self.overlay) };

		if self.commit_on_success {
			if res.is_err() {
				self.overlay.discard_prospective();
			} else {
				self.overlay.commit_prospective();
			}
		}

		res
	}
}
