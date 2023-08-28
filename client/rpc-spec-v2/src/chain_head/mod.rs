// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Substrate chain head API.
//!
//! # Note
//!
//! Methods are prefixed by `chainHead`.

#[cfg(test)]
mod test_utils;
#[cfg(test)]
mod tests;

pub mod api;
pub mod chain_head;
pub mod error;
pub mod event;

mod chain_head_follow;
mod chain_head_storage;
mod subscription;

pub use api::ChainHeadApiServer;
pub use chain_head::{ChainHead, ChainHeadConfig};
pub use event::{
	BestBlockChanged, ErrorEvent, Finalized, FollowEvent, Initialized, NewBlock, RuntimeEvent,
	RuntimeVersionEvent,
};

use sp_core::hexdisplay::{AsBytesRef, HexDisplay};

/// Util function to print the results of `chianHead` as hex string
pub(crate) fn hex_string<Data: AsBytesRef>(data: &Data) -> String {
	format!("0x{:?}", HexDisplay::from(data))
}
