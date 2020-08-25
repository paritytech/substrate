// Library shortcuts

use std::{pin::Pin};
use futures::{
	prelude::*,
	task::{Context, Poll},
};
use tokio::time::Duration;

use crate::rpc::{EngineCommand};

// ---
// Constant Definition

const DEFAULT_TIMEOUT: u64 = 30;
const DEFAULT_MIN_BLOCKTIME: u64 = 1;
const DEFAULT_FINALIZE: bool = false;

// ---
pub struct HeartbeatOptions {
	timeout: u64,
	min_blocktime: u64,
	finalize: bool,
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
	delay: tokio::time::Delay,
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
				// A new EngineCommand comes in
				hbs.delay = tokio::time::delay_for(Duration::from_secs(hbs.opts.timeout));
				Poll::Ready(Some(ec))
			},

			// The pool stream ends
			Poll::Ready(None) => Poll::Ready(None),

			Poll::Pending => {
				// We check if the delay for heartbeat has reached
				if let Poll::Ready(_) = hbs.delay.poll_unpin(cx) {
					hbs.delay = tokio::time::delay_for(Duration::from_secs(hbs.opts.timeout));
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
