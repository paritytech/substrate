use futures::{
	future::Future,
	stream::Stream,
	channel::{
		mpsc::{UnboundedSender, UnboundedReceiver, unbounded},
		oneshot::{Sender, Receiver, channel},
	},
};
use std::{pin::Pin, task::{Context, Poll}};
use sp_core::traits::BareCryptoStorePtr;

pub enum KeystoreRequest {
	Sign,
	Generate,
	Insert,
}

pub enum KeystoreResponse {
	Sign,
}

struct PendingCall {
	request: KeystoreRequest,
	sender: Sender<KeystoreResponse>,
	future: Pin<Box<dyn Future>>,
}

struct KeystoreProxy {
	store: BareCryptoStorePtr,
	sender: UnboundedSender<KeystoreRequest>,
	receiver: UnboundedReceiver<KeystoreRequest>,
}

impl KeystoreProxy {
	pub fn new(store: BareCryptoStorePtr) -> Self {
		let (sender, receiver) = unbounded::<KeystoreRequest>();

		KeystoreProxy{
			store,
			sender,
			receiver,
		}
	}

	pub fn sender(&self) -> UnboundedSender<KeystoreRequest> {
		self.sender.clone()
	}

	pub fn sign_with(&self) {
		let fut = self.keystore.sign_with();
	}
}

impl Future for KeystoreProxy {
	type Output = ();

	fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		if let Poll::Ready(Some(v)) = Pin::new(&mut self.receiver).poll_next(cx) {
			return Poll::Ready(());
		}

		return Poll::Pending;
	}
}
