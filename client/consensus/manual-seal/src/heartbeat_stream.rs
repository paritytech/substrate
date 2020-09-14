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
}

impl<Hash> Stream for HeartbeatStream<Hash> {
	type Item = EngineCommand<Hash>;

	fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
		match self.pool_stream.poll_next_unpin(cx) {
			Poll::Ready(Some(ec)) => {
				let HeartbeatOptions { heartbeat, cooldown, .. } = self.options;

				match (self.last_blocktime, cooldown) {
					(Some(last_blocktime), Some(cooldown)) => {
						let time_passed = Instant::now() - last_blocktime;
						if time_passed < cooldown {
							let wait_further = cooldown - time_passed;
							println!("poll_next: Cooling down, wait further for {:?}", wait_further);

							// We set `delay_future` here so it will wake up when the cooldown since the last
							//   block created is passed.
							self.delay_for = Some(Delay::new(wait_further));
							return Poll::Pending;
						}

						// tx come after cooldown period, we want to create block as normal
						println!("poll_next: Create block due to tx - last_blocktime, cooldown");
						// reset the timer and delay future
						self.delay_for = heartbeat.and_then(|hb| Some(Delay::new(hb)));
						self.last_blocktime = Some(Instant::now());
						Poll::Ready(Some(ec))
					},
					_ => {
						println!("poll_next: Create block due to tx");
						// reset the timer and delay future
						self.delay_for = heartbeat.and_then(|hb| Some(Delay::new(hb)));
						self.last_blocktime = Some(Instant::now());
						Poll::Ready(Some(ec))
					}
				}
			},

			// The pool stream ends
			Poll::Ready(None) => {
				println!("poll_next: None");
				Poll::Ready(None)
			},

			Poll::Pending => {
				let HeartbeatOptions { heartbeat, finalize, .. } = self.options;

				match &mut self.delay_for {
					Some(delay_for) => {

						// We check if the delay for heartbeat has reached
						if let Poll::Ready(_) = delay_for.poll_unpin(cx) {

							println!("poll_next: Creating heartbeat block");

							// reset the timer and delay future
							self.delay_for = heartbeat.and_then(|hb| Some(Delay::new(hb)));
							self.last_blocktime = Some(Instant::now());

							return Poll::Ready(Some(EngineCommand::SealNewBlock {
								create_empty: true, // new blocks created due to delay_future can be empty.
								finalize,
								parent_hash: None,
								sender: None,
							}));
						}

						println!("poll_next: Pending");
						Poll::Pending
					},
					None => {
						println!("poll_next: Pending");
						Poll::Pending
					}
				}
			}, // End of `Poll::Pending`

		}
	}
}
