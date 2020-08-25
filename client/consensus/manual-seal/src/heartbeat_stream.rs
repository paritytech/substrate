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

const HEARTBEAT_TIMEOUT: u64 = 30;

// ---

pub struct HeartbeatStream<Hash> {
	pool_stream: Box<dyn Stream<Item = EngineCommand<Hash>> + Unpin + Send>,
	delay: tokio::time::Delay,
}

impl<Hash> HeartbeatStream<Hash> {
	pub fn new(pool_stream: Box<dyn Stream<Item = EngineCommand<Hash>> + Unpin + Send>) -> Self {
		Self {
			pool_stream,
			delay: tokio::time::delay_for(Duration::from_secs(HEARTBEAT_TIMEOUT)),
		}
	}
}

impl<Hash> Stream for HeartbeatStream<Hash> {

	type Item = EngineCommand<Hash>;

	fn poll_next(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
		let mut hbs = self.get_mut();
		match hbs.pool_stream.poll_next_unpin(cx) {
			Poll::Ready(Some(ec)) => {
				hbs.delay = tokio::time::delay_for(Duration::from_secs(HEARTBEAT_TIMEOUT));
				Poll::Ready(Some(ec))
			},

			Poll::Ready(None) => Poll::Ready(None),

			Poll::Pending => {
				if let Poll::Ready(_) = hbs.delay.poll_unpin(cx) {
					hbs.delay = tokio::time::delay_for(Duration::from_secs(HEARTBEAT_TIMEOUT));
					return Poll::Ready(Some(EngineCommand::SealNewBlock {
						create_empty: true, // heartbeat blocks are empty by definition
						finalize: false,
						parent_hash: None,
						sender: None,
					}));
				}
				Poll::Pending
			},

		}
	}
}
