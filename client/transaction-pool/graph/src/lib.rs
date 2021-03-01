// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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

//! Generic Transaction Pool
//!
//! The pool is based on dependency graph between transactions
//! and their priority.
//! The pool is able to return an iterator that traverses transaction
//! graph in the correct order taking into account priorities and dependencies.

#![warn(missing_docs)]
#![warn(unused_extern_crates)]

mod future;
mod listener;
mod pool;
mod ready;
mod rotator;
mod validated_pool;
mod tracked_map;

pub mod base_pool;
pub mod watcher;

pub use self::base_pool::Transaction;
pub use self::pool::{
	BlockHash, ChainApi, EventStream, ExtrinsicFor, ExtrinsicHash, IsValidator, NumberFor, Options,
	Pool, TransactionFor, ValidatedTransaction,
};
