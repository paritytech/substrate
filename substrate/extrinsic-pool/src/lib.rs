// Copyright 2018 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

#![warn(missing_docs)]
#![warn(unused_extern_crates)]

//! Generic extrinsic pool.

extern crate futures;
extern crate parking_lot;
extern crate substrate_runtime_primitives as runtime_primitives;

#[macro_use]
extern crate log;
extern crate serde;
#[macro_use]
extern crate serde_derive;
extern crate transaction_pool as txpool;
#[cfg(test)] extern crate substrate_test_client as test_client;
#[cfg(test)] extern crate substrate_keyring as keyring;
#[cfg(test)] extern crate substrate_codec as codec;

pub mod watcher;
mod error;
mod listener;
mod pool;
mod rotator;

pub use listener::Listener;
pub use pool::{Pool, ChainApi, EventStream, Verified, VerifiedFor, ExtrinsicFor, ExHash, AllExtrinsics};
pub use txpool::scoring;
pub use txpool::{Error, ErrorKind};
pub use error::IntoPoolError;
pub use txpool::{Options, Status, LightStatus, VerifiedTransaction, Readiness, Transaction};
