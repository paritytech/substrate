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

//! Aura (Authority-round) consensus in substrate.
//!
//! Aura works by having a list of authorities A who are expected to roughly
//! agree on the current time. Time is divided up into discrete slots of t
//! seconds each. For each slot s, the author of that slot is A[s % |A|].
//!
//! The author is allowed to issue one block but not more during that slot,
//! and it will be built upon the longest valid chain that has been seen.
//!
//! Blocks from future steps will be either deferred or rejected depending on how
//! far in the future they are.

#![cfg_attr(not(feature = "std"), no_std)]

extern crate parity_codec as codec;
extern crate substrate_client as client;
extern crate substrate_primitives as primitives;
extern crate srml_support as runtime_support;
extern crate sr_io as runtime_io;
extern crate sr_primitives as runtime_primitives;
extern crate substrate_consensus_aura_primitives as aura_primitives;

#[cfg(feature = "std")]
extern crate substrate_consensus_common as consensus_common;
#[cfg(feature = "std")]
extern crate tokio;
#[cfg(feature = "std")]
extern crate sr_version as runtime_version;
#[cfg(feature = "std")]
extern crate substrate_network as network;
#[cfg(feature = "std")]
extern crate futures;
#[cfg(feature = "std")]
extern crate parking_lot;
#[cfg(feature = "std")]
#[macro_use]
extern crate log;

#[cfg(test)]
extern crate substrate_keyring as keyring;
#[cfg(test)]
extern crate substrate_service as service;
#[cfg(test)]
extern crate substrate_test_client as test_client;
#[cfg(test)]
extern crate env_logger;

#[cfg(feature = "std")]
mod consensus;

#[cfg(feature = "std")]
pub use consensus::*;

pub use aura_primitives::*;
