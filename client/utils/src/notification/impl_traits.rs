use super::*;

use ::futures::stream::{FusedStream, Stream};
use std::{
	pin::Pin,
	task::{Context, Poll},
};

impl<Payload> Clone for NotificationSender<Payload> {
	fn clone(&self) -> Self {
		Self { registry: self.registry.clone() }
	}
}

impl<Payload> Unpin for NotificationReceiver<Payload> {}

impl<Payload> Stream for NotificationReceiver<Payload> {
	type Item = Payload;

	fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Payload>> {
		Pin::new(self.get_mut().subs_guard.rx_mut()).poll_next(cx)
	}
}

impl<Payload> FusedStream for NotificationReceiver<Payload> {
	fn is_terminated(&self) -> bool {
		self.subs_guard.rx().is_terminated()
	}
}
