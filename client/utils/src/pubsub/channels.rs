use super::*;

use crate::mpsc;

#[derive(Debug, Copy)]
pub struct TracingUnbounded<Item> {
	key: &'static str,
	_pd: std::marker::PhantomData<Item>,
}

impl<Item> TracingUnbounded<Item> {
	pub fn new(key: &'static str) -> Self {
		Self { key, _pd: Default::default() }
	}
}

impl<Item> Clone for TracingUnbounded<Item> {
	fn clone(&self) -> Self {
		Self { key: self.key, _pd: Default::default() }
	}
}

impl<Item> Channel for TracingUnbounded<Item> {
	type Tx = mpsc::TracingUnboundedSender<Item>;
	type Rx = mpsc::TracingUnboundedReceiver<Item>;
	type Item = Item;

	fn create(&self) -> (Self::Tx, Self::Rx) {
		mpsc::tracing_unbounded(self.key)
	}

	fn send(&self, tx: &mut Self::Tx, item: Self::Item) {
		let _ = tx.unbounded_send(item);
	}
}
