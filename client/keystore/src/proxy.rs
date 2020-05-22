#![allow(dead_code)]
#![allow(missing_docs)]
use futures::{
	ready,
	future::Future,
	stream::{FuturesUnordered, Stream, StreamExt},
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

		let _ = sender.send(request).await;

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
	pending: FuturesUnordered<Pin<Box<dyn Future<Output = ()> + Send>>>,
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
		let sender = request.sender;
		match request.method {
			RequestMethod::SignWith(id, key, msg) => {
				let future = async move {
					let result = keystore.read().sign_with(id, &key, &msg).await;
					let _ = sender.send(KeystoreResponse::SignWith(result));
				};

				self.pending.push(Box::pin(future));
			},
			RequestMethod::HasKeys(keys) => {
				let future = async move {
					let result = keystore.read().has_keys(&keys).await;
					let _ = sender.send(KeystoreResponse::HasKeys(result));
				};

				self.pending.push(Box::pin(future));
			},
			RequestMethod::InsertUnknown(key_type, suri, pubkey) => {
				let future = async move {
					let result = keystore.write().insert_unknown(
						key_type,
						suri.as_str(),
						&pubkey,
					).await;
					let _ = sender.send(KeystoreResponse::InsertUnknown(result));
				};

				self.pending.push(Box::pin(future));
			}
		}
	}
}

impl Future for KeystoreReceiver {
	type Output = ();

	fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		loop {
			match self.pending.poll_next_unpin(cx) {
				Poll::Ready(Some(())) => {},
				Poll::Pending => break,
				Poll::Ready(None) => {
					// Stream has terminated
					// No need for this future to poll anymore.
					return Poll::Ready(());
				},
			}
		}

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
