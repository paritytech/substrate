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

//! Generic extrinsic pool.

extern crate futures;
extern crate parking_lot;
extern crate serde;

#[macro_use]
extern crate log;
#[macro_use]
extern crate serde_derive;

pub extern crate transaction_pool as txpool;

pub mod api;
pub mod watcher;

mod listener;
mod pool;

pub use self::listener::Listener;
pub use self::pool::Pool;
