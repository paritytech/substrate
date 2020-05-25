#![allow(dead_code)]
#![allow(missing_docs)]
use futures::{
	future::{Future, FutureExt},
	stream::Stream,
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
		BareCryptoStore,
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

enum State<Store: BareCryptoStore> {
	Idle(Store),
	Pending(Pin<Box<dyn Future<Output = Store> + Send>>),
	Poisoned,
}

pub struct KeystoreReceiver<Store: BareCryptoStore> {
	receiver: Receiver<KeystoreRequest>,
	state: State<Store>,
}

impl<Store: BareCryptoStore> Unpin for KeystoreReceiver<Store> {

}

impl<Store: BareCryptoStore + 'static> KeystoreReceiver<Store> {
	pub fn new(store: Store, receiver: Receiver<KeystoreRequest>) -> Self {
		KeystoreReceiver {
			receiver,
			state: State::Idle(store),
		}
	}

	fn process_request(store: Store, request: KeystoreRequest) -> Pin<Box<dyn Future<Output = Store> + Send>> {
		let sender = request.sender;
		match request.method {
			RequestMethod::SignWith(id, key, msg) => {
				Box::pin(async move {
					let result = store.sign_with(id, &key, &msg).await;
					let _ = sender.send(KeystoreResponse::SignWith(result));
					return store;
				})
			},
			RequestMethod::HasKeys(keys) => {
				Box::pin(async move {
					let result = store.has_keys(&keys).await;
					let _ = sender.send(KeystoreResponse::HasKeys(result));
					return store;
				})
			},
			RequestMethod::InsertUnknown(key_type, suri, pubkey) => {
				Box::pin(async move {
					let mut store = store;
					let result = store.insert_unknown(
						key_type,
						suri.as_str(),
						&pubkey,
					).await;
					let _ = sender.send(KeystoreResponse::InsertUnknown(result));
					return store;
				})
			}
		}
	}
}

impl<Store: BareCryptoStore + 'static> Future for KeystoreReceiver<Store> {
	type Output = ();

	fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		let this = &mut *self;
		loop {
			match std::mem::replace(&mut this.state, State::Poisoned) {
				State::Idle(store) => {
					match Pin::new(&mut this.receiver).poll_next(cx) {
						Poll::Ready(None) => {
							return Poll::Ready(());
						},
						Poll::Ready(Some(request)) => {
							let future = KeystoreReceiver::process_request(store, request);
							this.state = State::Pending(future);
						},
						Poll::Pending => {
							this.state = State::Idle(store);
						}
					}
				},
				State::Pending(mut future) => {
					match future.poll_unpin(cx) {
						Poll::Ready(store) => {
							this.state = State::Idle(store);
						},
						Poll::Pending => {
							this.state = State::Pending(future);
						}
					}
				},
				State::Poisoned => {
					unreachable!();
				}
			}
		}
	}
}

sp_externalities::decl_extension! {
	/// The keystore extension to register/retrieve from the externalities.
	pub struct KeystoreProxyExt(Arc<KeystoreProxy>);
}

pub fn proxy<Store: BareCryptoStore + 'static>(store: Store) -> (KeystoreProxy, KeystoreReceiver<Store>) {
	let (sender, receiver) = channel::<KeystoreRequest>(CHANNEL_SIZE);
	(KeystoreProxy::new(sender), KeystoreReceiver::new(store, receiver))
}
