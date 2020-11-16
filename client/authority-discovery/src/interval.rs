use futures::stream::Stream;
use futures::future::FutureExt;
use futures::ready;
use futures_timer::Delay;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::Duration;

/// Exponentially increasing interval
///
/// Doubles interval duration on each tick until the configured maximum is reached.
pub struct ExpIncInterval {
	max: Duration,
	next: Duration,
	delay: Delay,
}

impl ExpIncInterval {
	/// Create a new [`ExpIncInterval`].
	pub fn new(start: Duration, max: Duration) -> Self {
		let delay = Delay::new(start);
		Self {
			max,
			next: start * 2,
			delay,
		}
	}

	/// Fast forward the exponentially increasing interval to the configured maximum.
	pub fn set_to_max(&mut self) {
		self.next = self.max;
		self.delay = Delay::new(self.next);
	}
}

impl Stream for ExpIncInterval {
	type Item = ();

	fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
		ready!(self.delay.poll_unpin(cx));
		self.delay = Delay::new(self.next);
		self.next = std::cmp::min(self.max, self.next * 2);

		Poll::Ready(Some(()))
	}
}
