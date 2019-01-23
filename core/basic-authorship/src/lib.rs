// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

//! Basic implementation of block-authoring logic.

#![warn(unused_extern_crates)]

extern crate substrate_primitives as primitives;
extern crate sr_primitives as runtime_primitives;
extern crate substrate_consensus_common as consensus_common;
extern crate substrate_client as client;
extern crate parity_codec as codec;
extern crate substrate_transaction_pool as transaction_pool;
extern crate substrate_inherents as inherents;

#[macro_use]
extern crate log;

mod basic_authorship;

pub use basic_authorship::{ProposerFactory, BlockBuilder, AuthoringApi, Proposer};
