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

//! Generic Transaction Pool
//!
//! The pool is based on dependency graph between transactions
//! and their priority.
//! The pool is able to return an iterator that traverses transaction
//! graph in the correct order taking into account priorities and dependencies.
//!
//! TODO [ToDr]
//! - [ ] Multi-threading (getting ready transactions should not block the pool)

#![warn(missing_docs)]
#![warn(unused_extern_crates)]

extern crate futures;
extern crate parking_lot;
extern crate sr_primitives;

extern crate serde;
#[macro_use] extern crate error_chain;
#[macro_use] extern crate log;
#[macro_use] extern crate serde_derive;

#[cfg(test)]
extern crate substrate_test_runtime as test_runtime;
#[cfg(test)]
#[macro_use]
extern crate assert_matches;

mod future;
mod listener;
mod pool;
mod ready;
mod rotator;

pub mod base_pool;
pub mod error;
pub mod watcher;

pub use self::error::IntoPoolError;
pub use self::base_pool::{Transaction, Status};
pub use self::pool::{Pool, Options, ChainApi, EventStream, ExtrinsicFor, BlockHash, ExHash, NumberFor, TransactionFor};
