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
//! TODO: some more doc

use std::{pin::Pin, time::{Duration, Instant}};
use futures::{
	prelude::*,
	task::{Context, Poll},
};
use futures_timer::Delay;
use crate::rpc::EngineCommand;

/// Heartbeat options to manage the behavior of the heartbeat stream
pub struct HeartbeatOptions {
	/// The amount of time passed that a new heartbeat block will be generated when no transactions
	///   in tx pool, in sec.
	pub heartbeat: Option<Duration>,
	/// The cooldown time after a block has been authored, in sec.
	pub cooldown: Option<Duration>,
	pub finalize: bool,
}

impl Default for HeartbeatOptions {
	fn default() -> Self {
		Self {
			heartbeat: Some(Duration::from_secs(30)),
			cooldown: Some(Duration::from_secs(1)),
			finalize: false
		}
	}
}

/// HeartbeatStream is combining transaction pool notification stream and generate a new block
/// when a certain time has passed without any transactions.
pub struct HeartbeatStream<Hash> {
	/// The transaction pool notification stream
	pool_stream: Box<dyn Stream<Item = EngineCommand<Hash>> + Unpin + Send>,
	/// Future to control when the next block should be generated
	delay_for: Option<Delay>,
	/// To remember when the last block is generated
	last_blocktime: Option<Instant>,
	/// Heartbeat options
	options: HeartbeatOptions,
}

impl<Hash> HeartbeatStream<Hash> {
	pub fn new(
		pool_stream: Box<dyn Stream<Item = EngineCommand<Hash>> + Unpin + Send>,
		options: HeartbeatOptions,
	) -> Result<Self, &'static str> {
		if options.cooldown > options.heartbeat {
			return Err("Heartbeat options `cooldown` must not be larger than the `heartbeat` value.");
		}

		let delay_for = options.heartbeat.and_then(|hb| Some(Delay::new(hb)));
		Ok(Self {pool_stream, delay_for, last_blocktime: None, options})
	}

	fn create_block_now_and_reset_delay(&mut self) {
		self.last_blocktime = Some(Instant::now());
		self.delay_for = self.options.heartbeat.and_then(|hb| Some(Delay::new(hb)));
	}
}

impl<Hash> Stream for HeartbeatStream<Hash> {
	type Item = EngineCommand<Hash>;

	fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
		match self.pool_stream.poll_next_unpin(cx) {
			Poll::Ready(Some(ec)) => {
				let cooldown = self.options.cooldown;
				match (self.last_blocktime, cooldown) {
					(Some(last_blocktime), Some(cooldown)) => {
						// Illustration on variables used below:
						//      |------time_passed-------+------wait_further------|
						//   last blocktime           current                  cooldown
						//
						let time_passed = Instant::now() - last_blocktime;
						if time_passed < cooldown {
							let wait_further = cooldown - time_passed;
							println!("poll_next: tx come, but cooling down, wait for {:?}", wait_further);
							self.delay_for = Some(Delay::new(wait_further));
							// Since we set the `Delay` future above, we call `self.poll_next(cx)`, so it eventually
							//   polls the delay future.
							return self.poll_next(cx);
						}

						// txs come after cooldown period, so we want to create a block immediately
						println!("poll_next: Create block due to tx, after cooldown");
						self.create_block_now_and_reset_delay();
						Poll::Ready(Some(ec))
					},
					_ => {
						// Either no last_blocktime, so this is the first block created, or
						//   no `cooldown` in hearbeat option, so we don't need to check cooldown and create
						//   block immediately
						println!("poll_next: Create block due to tx, first block or no cooldown");
						self.create_block_now_and_reset_delay();
						Poll::Ready(Some(ec))
					}
				}
			},

			// The tx_pool stream comes to an end
			Poll::Ready(None) => {
				println!("poll_next: None");
				Poll::Ready(None)
			},

			// tx_pool pending. We want to check if we need to create a block due to delay_for has been set.
			//   `delay_for` is set when either there is a heartbeat (options.heartbeat is not `None`), or
			//   some txs come but the stream is still cooling down.
			Poll::Pending => {
				let finalize = self.options.finalize;
				match &mut self.delay_for {
					Some(delay_for) => {
						if let Poll::Ready(_) = delay_for.poll_unpin(cx) {
							println!("poll_next: Creating a block: delay_for ready");
							self.create_block_now_and_reset_delay();
							return Poll::Ready(Some(EngineCommand::SealNewBlock {
								create_empty: true, // new blocks created due to delay_future can be empty.
								finalize,
								parent_hash: None,
								sender: None,
							}));
						}

						println!("poll_next: Pending - delay_for not ready");
						Poll::Pending
					},
					None => {
						// `delay_for` is None. This is the case when no options.heartbeat is set.
						println!("poll_next: Pending - no heartbeat");
						Poll::Pending
					}
				}
			}, // End of `Poll::Pending`

		}
	}
}
