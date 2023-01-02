// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Block announcement validation.

use crate::BlockStatus;
use futures::FutureExt as _;
use sp_runtime::traits::Block;
use std::{error::Error, future::Future, pin::Pin, sync::Arc};

/// A type which provides access to chain information.
pub trait Chain<B: Block> {
	/// Retrieve the status of the block denoted by the given [`Block::Hash`].
	fn block_status(&self, hash: B::Hash) -> Result<BlockStatus, Box<dyn Error + Send>>;
}

impl<T: Chain<B>, B: Block> Chain<B> for Arc<T> {
	fn block_status(&self, hash: B::Hash) -> Result<BlockStatus, Box<dyn Error + Send>> {
		(&**self).block_status(hash)
	}
}

/// Result of `BlockAnnounceValidator::validate`.
#[derive(Debug, PartialEq, Eq)]
pub enum Validation {
	/// Valid block announcement.
	Success {
		/// Is this the new best block of the node?
		is_new_best: bool,
	},
	/// Invalid block announcement.
	Failure {
		/// Should we disconnect from this peer?
		///
		/// This should be used if the peer for example send junk to spam us.
		disconnect: bool,
	},
}

/// Type which checks incoming block announcements.
pub trait BlockAnnounceValidator<B: Block> {
	/// Validate the announced header and its associated data.
	///
	/// # Note
	///
	/// Returning [`Validation::Failure`] will lead to a decrease of the
	/// peers reputation as it sent us invalid data.
	///
	/// The returned future should only resolve to an error if there was an internal error
	/// validating the block announcement. If the block announcement itself is invalid, this should
	/// *always* return [`Validation::Failure`].
	fn validate(
		&mut self,
		header: &B::Header,
		data: &[u8],
	) -> Pin<Box<dyn Future<Output = Result<Validation, Box<dyn Error + Send>>> + Send>>;
}

/// Default implementation of `BlockAnnounceValidator`.
#[derive(Debug)]
pub struct DefaultBlockAnnounceValidator;

impl<B: Block> BlockAnnounceValidator<B> for DefaultBlockAnnounceValidator {
	fn validate(
		&mut self,
		_: &B::Header,
		data: &[u8],
	) -> Pin<Box<dyn Future<Output = Result<Validation, Box<dyn Error + Send>>> + Send>> {
		let is_empty = data.is_empty();

		async move {
			if !is_empty {
				log::debug!(
					target: "sync",
					"Received unknown data alongside the block announcement.",
				);
				Ok(Validation::Failure { disconnect: true })
			} else {
				Ok(Validation::Success { is_new_best: false })
			}
		}
		.boxed()
	}
}
