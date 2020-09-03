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
const DEFAULT_MAX_BLOCKTIME: u64 = 30;
const DEFAULT_MIN_BLOCKTIME: u64 = 1;
const DEFAULT_FINALIZE: bool = false;

/// Heartbeat options to manage the behavior of the heartbeat stream
pub struct HeartbeatOptions {
	/// The minimum amount of time to pass before generating a new block, in sec.
	pub min_blocktime: u64,
	/// The amount of time passed that a new heartbeat block will be generated, in sec.
	pub max_blocktime: u64,
	/// Control whether the generated block is finalized
	pub finalize: bool,
}

impl Default for HeartbeatOptions {
	fn default() -> Self {
		Self {
			min_blocktime: DEFAULT_MIN_BLOCKTIME,
			max_blocktime: DEFAULT_MAX_BLOCKTIME,
			finalize: DEFAULT_FINALIZE,
		}
	}
}

/// HeartbeatStream is combining transaction pool notification stream and generate a new block
///   when a certain time has passed without any transactions.
pub struct HeartbeatStream<Hash> {
	/// The transaction pool notification stream
	pool_stream: Box<dyn Stream<Item = EngineCommand<Hash>> + Unpin + Send>,
	/// Future to control when the next block should be generated
	delay_future: Delay,
	/// To remember when the last block is generated
	last_blocktime: Option<Instant>,
	/// Heartbeat options
	opts: HeartbeatOptions,
}

impl<Hash> HeartbeatStream<Hash> {
	pub fn new(
		pool_stream: Box<dyn Stream<Item = EngineCommand<Hash>> + Unpin + Send>,
		opts: HeartbeatOptions
	) -> Self {
		if opts.min_blocktime > opts.max_blocktime {
			panic!("Heartbeat options `min_blocktime` value must not be larger than `max_blocktime` value.");
		}
		Self {
			pool_stream,
			delay_future: tokio::time::delay_for(Duration::from_secs(opts.max_blocktime)),
			last_blocktime: None,
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
				if let Some(last_blocktime) = hbs.last_blocktime {
					// If the last block happened less than the min_blocktime time, we want to wait till
					//   `min_blocktime` has lapsed.
					let passed_blocktime = Instant::now() - last_blocktime;
					if passed_blocktime < Duration::from_secs(hbs.opts.min_blocktime) {
						// We set `delay_future` here so it will wake up when the min_blocktime since the last
						//   block created is passed.
						hbs.delay_future = tokio::time::delay_for(Duration::from_secs(hbs.opts.min_blocktime)
							- passed_blocktime);
						return Poll::Pending;
					}
				}

				// reset the timer and delay future
				hbs.delay_future = tokio::time::delay_for(Duration::from_secs(hbs.opts.max_blocktime));
				hbs.last_blocktime = Some(Instant::now());
				Poll::Ready(Some(ec))
			},

			// The pool stream ends
			Poll::Ready(None) => Poll::Ready(None),

			Poll::Pending => {
				// We check if the delay for heartbeat has reached
				if let Poll::Ready(_) = hbs.delay_future.poll_unpin(cx) {
					// reset the timer and delay future
					hbs.delay_future = tokio::time::delay_for(Duration::from_secs(hbs.opts.max_blocktime));
					hbs.last_blocktime = Some(Instant::now());

					return Poll::Ready(Some(EngineCommand::SealNewBlock {
						create_empty: true, // new blocks created due to delay_future can be empty.
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
