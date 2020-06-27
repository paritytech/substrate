// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

use serde::{Serialize, Deserialize};
use sp_runtime::traits::Block as BlockT;

/// Justification for a finalized block.
#[derive(Clone, Serialize, Deserialize)]
pub struct JustificationNotification<Block: BlockT> {
	/// Highest finalized block header
	pub header: Block::Header,
	/// An encoded justification proving that the given header has been finalized
	pub justification: Vec<u8>,
}

impl<Block: BlockT> From<(Block::Header, Vec<u8>)> for JustificationNotification<Block> {
	fn from(notification: (Block::Header, Vec<u8>)) -> Self {
		JustificationNotification {
			header: notification.0,
			justification: notification.1,
		}
	}
}