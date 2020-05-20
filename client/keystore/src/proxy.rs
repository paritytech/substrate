#![allow(dead_code)]
#![allow(missing_docs)]
use futures::{
	ready,
	future::Future,
	stream::{Stream, FuturesUnordered},
	channel::{
		oneshot,
		mpsc::{Sender, Receiver, channel},
	},
};
use futures_util::sink::SinkExt;
use std::{
	pin::Pin,
	sync::Arc,
	task::{Context, Poll}
};
use sp_core::{
	crypto::{
		CryptoTypePublicPair,
		KeyTypeId,
	},
	traits::{
		BareCryptoStorePtr,
		BareCryptoStoreError,
	},
};
pub use sp_externalities::{Externalities, ExternalitiesExt};

const CHANNEL_SIZE: usize = 128;

pub enum RequestMethod {
	SignWith(KeyTypeId, CryptoTypePublicPair, Vec<u8>),
	HasKeys(Vec<(Vec<u8>, KeyTypeId)>),
	InsertUnknown(KeyTypeId, String, Vec<u8>),
}

pub struct KeystoreRequest {
	sender: oneshot::Sender<KeystoreResponse>,
	method: RequestMethod,
}

pub enum KeystoreResponse {
	SignWith(Result<Vec<u8>, BareCryptoStoreError>),
	HasKeys(bool),
	InsertUnknown(Result<(), ()>),
}

pub enum PendingFuture {
	SignWith(Pin<Box<dyn Future<Output = Result<Vec<u8>, BareCryptoStoreError>>>>),
	HasKeys(Pin<Box<dyn Future<Output = bool>>>),
	InsertUnknown(Pin<Box<dyn Future<Output = Result<(), ()>>>>),
}

struct PendingCall {
	future: PendingFuture,
	sender: oneshot::Sender<KeystoreResponse>,
}

pub struct KeystoreProxy {
	sender: Sender<KeystoreRequest>,
}

impl KeystoreProxy {
	pub fn new(sender: Sender<KeystoreRequest>) -> Self {
		KeystoreProxy {
			sender,
		}
	}

	async fn send_request(
		&self,
		request: RequestMethod
	) -> Result<KeystoreResponse, oneshot::Canceled> {
		let (request_sender, request_receiver) = oneshot::channel::<KeystoreResponse>();

		let request = KeystoreRequest {
			sender: request_sender,
			method: request,
		};
		let mut sender = self.sender.clone();

		sender.send(request).await;

		request_receiver.await
	}

	pub async fn sign_with(
		&self,
		id: KeyTypeId,
		key: &CryptoTypePublicPair,
		msg: &[u8],
	) -> Result<KeystoreResponse, oneshot::Canceled> {
		self.send_request(RequestMethod::SignWith(id, key.clone(), msg.to_vec())).await
	}

	pub async fn has_keys(
		&self,
		public_keys: &[(Vec<u8>, KeyTypeId)]
	) -> Result<KeystoreResponse, oneshot::Canceled> {
		self.send_request(RequestMethod::HasKeys(public_keys.to_vec())).await
	}

	pub async fn insert_unknown(
		&self,
		key_type: KeyTypeId,
		suri: &str,
		public: &[u8]
	) -> Result<KeystoreResponse, oneshot::Canceled> {
		self.send_request(RequestMethod::InsertUnknown(
			key_type,
			suri.to_string(),
			public.to_vec(),
		)).await
	}
}

pub struct KeystoreReceiver {
	receiver: Receiver<KeystoreRequest>,
	store: BareCryptoStorePtr,
	pending: FuturesUnordered<PendingCall>,
}

impl KeystoreReceiver {
	pub fn new(store: BareCryptoStorePtr, receiver: Receiver<KeystoreRequest>) -> Self {
		KeystoreReceiver {
			receiver,
			store,
			pending: FuturesUnordered::new(),
		}
	}

	fn process_request(&mut self, request: KeystoreRequest) {
		let keystore = self.store.clone();
		match request.method {
			RequestMethod::SignWith(id, key, msg) => {
				let future = async move {
					keystore.read().sign_with(id, &key, &msg).await
				};

				self.pending.push(PendingCall {
					future: PendingFuture::SignWith(Box::pin(future)),
					sender: request.sender,
				});
			},
			RequestMethod::HasKeys(keys) => {
				let future = async move {
					keystore.read().has_keys(&keys).await
				};

				self.pending.push(PendingCall {
					future: PendingFuture::HasKeys(Box::pin(future)),
					sender: request.sender,
				});
			},
			RequestMethod::InsertUnknown(key_type, suri, pubkey) => {
				let future = async move {
					keystore.write().insert_unknown(
						key_type,
						suri.as_str(),
						&pubkey,
					).await
				};

				self.pending.push(PendingCall {
					future: PendingFuture::InsertUnknown(Box::pin(future)),
					sender: request.sender,
				});
			}
		}
	}
}

impl Future for PendingFuture {
	type Output = KeystoreResponse;
	fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		match self.get_mut() {
			PendingFuture::HasKeys(fut) => {
				if let Poll::Ready(result) = fut.as_mut().poll(cx) {
					return Poll::Ready(KeystoreResponse::HasKeys(result));
				}
			},
			PendingFuture::InsertUnknown(fut) => {
				if let Poll::Ready(result) = fut.as_mut().poll(cx) {
					return Poll::Ready(KeystoreResponse::InsertUnknown(result));
				}
			},
			PendingFuture::SignWith(fut) => {
				if let Poll::Ready(result) = fut.as_mut().poll(cx) {
					return Poll::Ready(KeystoreResponse::SignWith(result));
				}
			}
		}
		return Poll::Pending;
	}
}

impl Future for PendingCall {
	type Output = ();
	fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		let sender = &mut self.sender;
		if let Poll::Ready(response) = Pin::new(&mut self.future).poll(cx) {
			sender.send(response);
		}
		// match &mut self.future {
		// 	PendingFuture::HasKeys(fut) => {
		// 		if let Poll::Ready(result) = fut.as_mut().poll(cx) {
		// 			self.sender.send(KeystoreResponse::HasKeys(result));
		// 			return Poll::Ready(());
		// 		}
		// 	},
		// 	PendingFuture::InsertUnknown(fut) => {
		// 		if let Poll::Ready(result) = fut.as_mut().poll(cx) {
		// 			self.sender.send(KeystoreResponse::InsertUnknown(result));
		// 			return Poll::Ready(());
		// 		}
		// 	},
		// 	PendingFuture::SignWith(fut) => {
		// 		if let Poll::Ready(result) = fut.as_mut().poll(cx) {
		// 			self.sender.send(KeystoreResponse::SignWith(result));
		// 			return Poll::Ready(());
		// 		}
		// 	}
		// }
		// if let Some(call) = ready!(self.future.poll()) {
		// 	self.sender.start_send(call);
		// }
		return Poll::Pending;
	}
}

impl Future for KeystoreReceiver {
	type Output = ();

	fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {

		// for item in self.pending.iter_mut() {
		// 	match pending.future {
		// 		PendingFuture::SignWith(mut future) => {
		// 			future.as_mut().poll(cx);
		// 		},
		// 		PendingFuture::HasKeys(mut future) => {
		// 			future.as_mut().poll(cx);
		// 		},
		// 		PendingFuture::InsertUnknown(mut future) => {
		// 			future.as_mut().poll(cx);
		// 		}
		// 	}
		// }
		Pin::new(&mut self.pending).poll_next(cx);
	
		if let Some(request) = ready!(Pin::new(&mut self.receiver).poll_next(cx)) {
			self.process_request(request);
		}

		return Poll::Pending;
	}
}

sp_externalities::decl_extension! {
	/// The keystore extension to register/retrieve from the externalities.
	pub struct KeystoreProxyExt(Arc<KeystoreProxy>);
}

pub fn proxy(store: BareCryptoStorePtr) -> (KeystoreProxy, KeystoreReceiver) {
	let (sender, receiver) = channel::<KeystoreRequest>(CHANNEL_SIZE);
	(KeystoreProxy::new(sender), KeystoreReceiver::new(store, receiver))
}
