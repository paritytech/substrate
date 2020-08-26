// Library shortcuts

use std::{pin::Pin};
use futures::{
	prelude::*,
	task::{Context, Poll},
};
use tokio::time::{Duration, Instant, Delay};

use crate::rpc::{EngineCommand};

// ---
// Constant Definition

const DEFAULT_TIMEOUT: u64 = 30;
const DEFAULT_MIN_BLOCKTIME: u64 = 1;
const DEFAULT_FINALIZE: bool = false;

// ---
pub struct HeartbeatOptions {
	pub timeout: u64,
	pub min_blocktime: u64,
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

pub struct HeartbeatStream<Hash> {
	pool_stream: Box<dyn Stream<Item = EngineCommand<Hash>> + Unpin + Send>,
	delay: Delay,
	instant: Instant,
	opts: HeartbeatOptions,
}

impl<Hash> HeartbeatStream<Hash> {
	pub fn new(
		pool_stream: Box<dyn Stream<Item = EngineCommand<Hash>> + Unpin + Send>,
		opts: HeartbeatOptions
	) -> Self {
		Self {
			pool_stream,
			delay: tokio::time::delay_for(Duration::from_secs(opts.timeout)),
			instant: Instant::now(),
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
				// Ensure we are not producing block too frequently, based on `min_blocktime` setting
				if Instant::now() - hbs.instant < Duration::from_secs(hbs.opts.min_blocktime) {
					return Poll::Pending;
				}

				// reset the timer and delay future
				hbs.delay = tokio::time::delay_for(Duration::from_secs(hbs.opts.timeout));
				hbs.instant = Instant::now();
				Poll::Ready(Some(ec))
			},

			// The pool stream ends
			Poll::Ready(None) => Poll::Ready(None),

			Poll::Pending => {
				// We check if the delay for heartbeat has reached
				if let Poll::Ready(_) = hbs.delay.poll_unpin(cx) {
					// reset the timer and delay future
					hbs.delay = tokio::time::delay_for(Duration::from_secs(hbs.opts.timeout));
					hbs.instant = Instant::now();

					return Poll::Ready(Some(EngineCommand::SealNewBlock {
						create_empty: true, // heartbeat blocks are empty by definition
						finalize: hbs.opts.finalize,
						parent_hash: None, // QUESTION: no parent hash here? Is this block still conneected with the whole chain?
						sender: None,
					}));
				}
				Poll::Pending
			},
		}
	}
}
