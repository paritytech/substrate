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
mod tests;

pub mod api;
pub mod chain_head;
pub mod error;
pub mod event;

mod subscription;

pub use api::ChainHeadApiServer;
pub use chain_head::ChainHead;
pub use event::{
	BestBlockChanged, ChainHeadEvent, ChainHeadResult, ErrorEvent, Finalized, FollowEvent,
	Initialized, NetworkConfig, NewBlock, RuntimeEvent, RuntimeVersionEvent,
};
