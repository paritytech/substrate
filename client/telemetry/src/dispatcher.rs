use futures::prelude::*;
use std::collections::HashMap;
use crate::node::{Node, Infallible};
use crate::worker::WsTrans;
use std::iter::FromIterator;
use libp2p::Multiaddr;
use std::task::{Poll, Context};
use std::pin::Pin;

#[derive(Debug)]
pub(crate) struct Dispatcher {
	pool: HashMap<Multiaddr, Node<WsTrans>>,
	item: Option<(Multiaddr, String)>,
	flush_node: Option<Multiaddr>,
}

impl FromIterator<(Multiaddr, Node<WsTrans>)> for Dispatcher {
	fn from_iter<I: IntoIterator<Item=(Multiaddr, Node<WsTrans>)>>(iter: I) -> Self {
		let pool: HashMap<_, _> = FromIterator::from_iter(iter);
		Dispatcher {
			pool,
			item: None,
			flush_node: None,
		}
	}
}

impl Dispatcher {
	fn try_empty_buffer(
		mut self: Pin<&mut Self>,
		cx: &mut Context<'_>,
	) -> Poll<Result<(), Infallible>> {
		if let Some((addr, message)) = self.item.take() {
			let node = if let Some(node) = self.pool.get_mut(&addr) {
				node
			} else {
				log::error!(
					target: "telemetry",
					"Received message for unknown node ({}). This is a bug. Message sent: {}",
					addr,
					message,
				);
				return Poll::Ready(Ok(()));
			};

			match node.poll_ready_unpin(cx) {
				Poll::Ready(Ok(())) => {},
				Poll::Ready(Err(x)) => match x {},
				Poll::Pending => {
					self.item = Some((addr, message));
					return Poll::Pending;
				}
			}

			match node.start_send_unpin(message) {
				Ok(()) => {},
				Err(x) => match x {},
			}

			match node.poll_flush_unpin(cx) {
				Poll::Ready(Ok(())) => {},
				Poll::Ready(Err(x)) => match x {},
				Poll::Pending => {
					self.flush_node = Some(addr);
					return Poll::Pending;
				},
			}
		}

		Poll::Ready(Ok(()))
	}
}

impl Sink<(Multiaddr, String)> for Dispatcher
{
	type Error = Infallible;

	fn poll_ready(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Result<(), Self::Error>> {
		self.try_empty_buffer(cx)
	}

	fn start_send(mut self: Pin<&mut Self>, item: (Multiaddr, String)) -> Result<(), Self::Error> {
		let overrun = self.item.replace(item).is_some();

		if overrun {
			log::error!(
				target: "telemetry",
				"Received another message while the previous one has not finished processing. \
				This is a bug",
			);
		}

		Ok(())
	}

	fn poll_flush(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
		if let Some(addr) = self.flush_node.take() {
			let node = self.pool.get_mut(&addr).expect("we added the address ourselves; qed");
			match node.poll_flush_unpin(cx) {
				Poll::Ready(Ok(())) => return Poll::Ready(Ok(())),
				Poll::Ready(Err(x)) => match x {},
				Poll::Pending => {
					self.flush_node = Some(addr);
					return Poll::Pending;
				},
			}
		}

		self.try_empty_buffer(cx)
	}

	fn poll_close(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
		let mut new_pool = HashMap::with_capacity(self.pool.len());

		for (addr, mut node) in self.pool.drain() {
			match node.poll_close_unpin(cx) {
				Poll::Ready(Ok(())) => {},
				Poll::Ready(Err(x)) => match x {},
				Poll::Pending => {
					new_pool.insert(addr, node);
				},
			}
		}

		let _ = std::mem::replace(&mut self.pool, new_pool);

		if self.pool.is_empty() {
			Poll::Ready(Ok(()))
		} else {
			Poll::Pending
		}
	}
}
