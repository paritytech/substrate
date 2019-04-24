// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
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

pub mod base_pool;
pub mod error;
pub mod watcher;

pub use self::error::IntoPoolError;
pub use self::base_pool::{Transaction, Status};
pub use self::pool::{Pool, Options, ChainApi, EventStream, ExtrinsicFor, BlockHash, ExHash, NumberFor, TransactionFor};
