// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Aura consensus algorithm, implemented for substrate.
//!
//! This works with a list of authorities A and monotonic time clock.
//! Time is divided into discrete steps. For each time step T, an authority
//! is chosen from the list as `A[T % len(A)]` and has the chance to author
//! a block.

extern crate parity_codec as codec;
extern crate substrate_primitives as primitives;
extern crate srml_support as runtime_support;
extern crate sr_primitives as runtime_primitives;
extern crate sr_version as runtime_version;
extern crate sr_io as runtime_io;
extern crate tokio;

#[cfg(test)]
extern crate substrate_keyring as keyring;
extern crate parking_lot;
extern crate rhododendron;

#[macro_use]
extern crate log;


extern crate futures;

#[macro_use]
extern crate error_chain;

#[macro_use]
extern crate serde;

#[macro_use]
extern crate parity_codec_derive;

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Instant, Duration};

use codec::Encode;
use runtime_primitives::{generic::BlockId, Justification};
use runtime_primitives::traits::{Block, Header};
use primitives::{AuthorityId, ed25519, ed25519::LocalizedSignature};

use futures::{Async, Stream, Sink, Future, IntoFuture};
use futures::sync::oneshot;
use tokio::timer::Delay;
use parking_lot::Mutex;
