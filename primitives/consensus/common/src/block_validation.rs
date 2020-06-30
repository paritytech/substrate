// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.
//
// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Block announcement validation.

use crate::BlockStatus;
use sp_runtime::{generic::BlockId, traits::Block};
use std::{error::Error, sync::Arc};

/// A type which provides access to chain information.
pub trait Chain<B: Block> {
	/// Retrieve the status of the block denoted by the given [`BlockId`].
	fn block_status(&self, id: &BlockId<B>) -> Result<BlockStatus, Box<dyn Error + Send>>;
}

impl<T: Chain<B>, B: Block> Chain<B> for Arc<T> {
	fn block_status(&self, id: &BlockId<B>) -> Result<BlockStatus, Box<dyn Error + Send>> {
		(&**self).block_status(id)
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
	Failure,
}

/// Type which checks incoming block announcements.
pub trait BlockAnnounceValidator<B: Block> {
	/// Validate the announced header and its associated data.
	fn validate(&mut self, header: &B::Header, data: &[u8]) -> Result<Validation, Box<dyn Error + Send>>;
}

/// Default implementation of `BlockAnnounceValidator`.
#[derive(Debug)]
pub struct DefaultBlockAnnounceValidator;

impl<B: Block> BlockAnnounceValidator<B> for DefaultBlockAnnounceValidator {
	fn validate(&mut self, _h: &B::Header, _d: &[u8]) -> Result<Validation, Box<dyn Error + Send>> {
		Ok(Validation::Success { is_new_best: false })
	}
}
