// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! HeartbeatStream type and HeartbeatOptions used in instant seal
use std::{pin::Pin};
use futures::{
	prelude::*,
	task::{Context, Poll},
};
use tokio::time::{Duration, Instant, Delay};

use crate::rpc::{EngineCommand};

/// Constants for generating default heartbeat options
const DEFAULT_TIMEOUT: u64 = 30;
const DEFAULT_MIN_BLOCKTIME: u64 = 1;
const DEFAULT_FINALIZE: bool = false;

/// Heartbeat options to manage the behavior of the heartbeat stream
pub struct HeartbeatOptions {
	/// The amount of time passed that a new heartbeat block will be generated, in sec.
	pub timeout: u64,
	/// The minimum amount of time to pass before generating another block, in sec.
	pub min_blocktime: u64,
	/// Control whether the generated heartbeat block is finalized
	pub finalize: bool,
}

impl Default for HeartbeatOptions {
	fn default() -> Self {
		Self {
			timeout: DEFAULT_TIMEOUT,
			min_blocktime: DEFAULT_MIN_BLOCKTIME,
			finalize: DEFAULT_FINALIZE,
		}
	}
}

/// HeartbeatStream is combining transaction pool notification stream and generate heartbeat
///   blocks when a certain time has passed without any transactions.
pub struct HeartbeatStream<Hash> {
	/// The transaction pool notification stream
	pool_stream: Box<dyn Stream<Item = EngineCommand<Hash>> + Unpin + Send>,
	/// Future to control when the next heartbeat block should be generated
	delay_future: Delay,
	/// To remember when the last heartbeat block is generated
	last_heartbeat: Option<Instant>,
	/// Heartbeat options
	opts: HeartbeatOptions,
}

impl<Hash> HeartbeatStream<Hash> {
	pub fn new(
		pool_stream: Box<dyn Stream<Item = EngineCommand<Hash>> + Unpin + Send>,
		opts: HeartbeatOptions
	) -> Self {
		if opts.min_blocktime > opts.timeout {
			panic!("Heartbeat options `min_blocktime` value must not be larger than `timeout` value.");
		}
		Self {
			pool_stream,
			delay_future: tokio::time::delay_for(Duration::from_secs(opts.timeout)),
			last_heartbeat: None,
			opts
		}
	}
}

impl<Hash> Stream for HeartbeatStream<Hash> {

	type Item = EngineCommand<Hash>;

	fn poll_next(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
		let mut hbs = self.get_mut();
		match hbs.pool_stream.poll_next_unpin(cx) {
			Poll::Ready(Some(ec)) => {
				if let Some(last_heartbeat) = hbs.last_heartbeat {
					// If the last heartbeat happened within min_blocktime time, we want to wait at least
					//   until `min_blocktime` has passed.
					if Instant::now() - last_heartbeat < Duration::from_secs(hbs.opts.min_blocktime) {
						// We set `delay_future` here so those txs arrived after heartbeats doesn't have to wait
						//   for `timeout`s to get processed, but only `min_blocktime`s.
						hbs.delay_future = tokio::time::delay_for(Duration::from_secs(hbs.opts.min_blocktime));
						return Poll::Pending;
					}
				}

				// reset the timer and delay future
				hbs.delay_future = tokio::time::delay_for(Duration::from_secs(hbs.opts.timeout));
				hbs.last_heartbeat = Some(Instant::now());
				Poll::Ready(Some(ec))
			},

			// The pool stream ends
			Poll::Ready(None) => Poll::Ready(None),

			Poll::Pending => {
				// We check if the delay for heartbeat has reached
				if let Poll::Ready(_) = hbs.delay_future.poll_unpin(cx) {
					// reset the timer and delay future
					hbs.delay_future = tokio::time::delay_for(Duration::from_secs(hbs.opts.timeout));
					hbs.last_heartbeat = Some(Instant::now());

					return Poll::Ready(Some(EngineCommand::SealNewBlock {
						create_empty: true, // heartbeat blocks are empty by definition
						finalize: hbs.opts.finalize,
						parent_hash: None,
						sender: None,
					}));
				}
				Poll::Pending
			},
		}
	}
}
