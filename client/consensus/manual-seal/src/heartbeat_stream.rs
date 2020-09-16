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

//! Heartbeat stream is a stream adapter built around the manual-seal `EngineCommand` stream.
//! It adds additional logic of creating heartbeat block and having a cooldown period.

use std::{pin::Pin, time::{Duration, Instant}};
use futures::{
	prelude::*,
	task::{Context, Poll},
};
use futures_timer::Delay;
use crate::rpc::EngineCommand;

/// Options to manage the behavior of the heartbeat stream
struct Options {
	// The amount of time passed that a new empty block will be generated when no transactions
	// in the tx pool.
	heartbeat: Option<Duration>,
	// The cooldown duration after a block has been authored.
	cooldown: Option<Duration>,
	// Whether the created block is finalized of not.
	finalize: bool,
}

/// Heartbeat stream is a stream adapter built around the manual-seal `EngineCommand` stream.
/// It adds additional logic of creating heartbeat block and having a cooldown period.
pub struct HeartbeatStream<Hash> {
	// The `EngineCommand` stream passed from the caller
	command_stream: Box<dyn Stream<Item = EngineCommand<Hash>> + Unpin + Send>,
	// Delay future to control when to wake up next
	delay_for: Option<Delay>,
	// To remember when the last block is generated
	last_blocktime: Option<Instant>,
	// Heartbeat options
	options: Options,
}

impl<Hash> HeartbeatStream<Hash> {
	pub fn new(
		command_stream: Box<dyn Stream<Item = EngineCommand<Hash>> + Unpin + Send>,
		heartbeat: Option<Duration>,
		cooldown: Option<Duration>,
		finalize: bool
	) -> Result<Self, &'static str> {
		match (heartbeat, cooldown) {
			(Some(heartbeat), Some(cooldown)) if cooldown > heartbeat =>
				Err("`cooldown` must not be larger than the `heartbeat`, if they are both set."),
			_ => Ok(()),
		}?;

		let delay_for = heartbeat.and_then(|hb| Some(Delay::new(hb)));
		Ok(Self {
			command_stream,
			delay_for,
			last_blocktime: None,
			options: Options { heartbeat, cooldown, finalize }
		})
	}

	fn create_block_now_and_reset_delay(&mut self) {
		self.last_blocktime = Some(Instant::now());
		self.delay_for = self.options.heartbeat.and_then(|hb| Some(Delay::new(hb)));
	}
}

impl<Hash> Stream for HeartbeatStream<Hash> {
	type Item = EngineCommand<Hash>;

	fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
		match self.command_stream.poll_next_unpin(cx) {

			Poll::Ready(Some(ec)) => {
				// An engine command comes in, meaning a transaction in `tx_pool` now
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
							self.delay_for = Some(Delay::new(wait_further));
							// Since we set the `Delay` future above, we call `self.poll_next(cx)`, so it eventually
							//   polls the delay future.
							return self.poll_next(cx);
						}

						// txs come after cooldown period, so we want to create a block immediately
						self.create_block_now_and_reset_delay();
						Poll::Ready(Some(ec))
					},
					_ => {
						// Either no `last_blocktime`, so this is the first block created, or
						//   no `cooldown` in hearbeat option, so we don't need to check cooldown and create
						//   block immediately
						self.create_block_now_and_reset_delay();
						Poll::Ready(Some(ec))
					}
				}
			},

			// `EngineCommand` stream pending, meaning no txs in `tx_pool`. We want to check if we need
			// to create a block due to `delay_for` is waking up.
			// `delay_for` is set when either heartbeat duration is specified, or some txs has come
			// but the stream was still cooling down.
			Poll::Pending => {
				let finalize = self.options.finalize;
				match &mut self.delay_for {
					Some(delay_for) => {
						if let Poll::Ready(_) = delay_for.poll_unpin(cx) {
							self.create_block_now_and_reset_delay();
							return Poll::Ready(Some(EngineCommand::SealNewBlock {
								// New blocks created can be empty as it may just be an empty heartbeat block.
								create_empty: true,
								finalize,
								parent_hash: None,
								sender: None,
							}));
						}

						Poll::Pending
					},
					None => Poll::Pending,
				}
			}, // End of `Poll::Pending`

			// The `EngineCommand` stream comes to an end
			Poll::Ready(None) => Poll::Ready(None),
		}
	}
}
