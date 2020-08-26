#![allow(dead_code)]
#![allow(missing_docs)]
use async_trait::async_trait;
use parking_lot::RwLock;
use futures::{
	channel::{
		oneshot,
		mpsc::{Sender, Receiver, channel},
	},
	future::{Future, FutureExt},
	stream::Stream,
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
	ecdsa,
	ed25519,
	sr25519,
	traits::{
		BareCryptoStore,
		Error as BareCryptoStoreError,
	},
};
pub use sp_externalities::{Externalities, ExternalitiesExt};

const CHANNEL_SIZE: usize = 128;

pub enum RequestMethod {
	Sr25519PublicKeys(KeyTypeId),
	Sr25519GenerateNew(KeyTypeId, Option<String>),
	Sr25519VrfSign(
		KeyTypeId,
		sp_application_crypto::sr25519::Public,
		sp_core::vrf::VRFTranscriptData,
	),
	Ed25519PublicKeys(KeyTypeId),
	Ed25519GenerateNew(KeyTypeId, Option<String>),
	EcdsaPublicKeys(KeyTypeId),
	EcdsaGenerateNew(KeyTypeId, Option<String>),
	InsertUnknown(KeyTypeId, String, Vec<u8>),
	Password,
	SupportedKeys(KeyTypeId, Vec<CryptoTypePublicPair>),
	Keys(KeyTypeId,),
	HasKeys(Vec<(Vec<u8>, KeyTypeId)>),
	SignWith(KeyTypeId, CryptoTypePublicPair, Vec<u8>),
}

pub struct KeystoreRequest {
	sender: oneshot::Sender<KeystoreResponse>,
	method: RequestMethod,
}

pub enum KeystoreResponse {
	Sr25519PublicKeys(Vec<sr25519::Public>),
	Sr25519GenerateNew(
		Result<sp_application_crypto::sr25519::Public, BareCryptoStoreError>
	),
	Sr25519VrfSign(
		Result<sp_core::vrf::VRFSignature, BareCryptoStoreError>
	),
	Ed25519PublicKeys(Vec<ed25519::Public>),
	Ed25519GenerateNew(
		Result<sp_application_crypto::ed25519::Public, BareCryptoStoreError>
	),
	EcdsaPublicKeys(Vec<ecdsa::Public>),
	EcdsaGenerateNew(
		Result<sp_application_crypto::ecdsa::Public, BareCryptoStoreError>
	),
	InsertUnknown(Result<(), ()>),
	Password(Option<String>),
	SupportedKeys(Result<Vec<CryptoTypePublicPair>, BareCryptoStoreError>),
	Keys(Result<Vec<CryptoTypePublicPair>, BareCryptoStoreError>),
	HasKeys(bool),
	SignWith(Result<Vec<u8>, BareCryptoStoreError>),
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
}

#[async_trait]
impl BareCryptoStore for KeystoreProxy {
    async fn sr25519_public_keys(&self, id: KeyTypeId) -> Vec<sp_application_crypto::sr25519::Public> {
		let response = self.send_request(RequestMethod::Sr25519PublicKeys(id)).await;
		match response {
			Ok(KeystoreResponse::Sr25519PublicKeys(keys)) => keys,
			_ => vec![],
		}
    }

    async fn sr25519_generate_new(
		&mut self,
		id: KeyTypeId,
		seed: Option<&str>,
	) -> Result<sp_application_crypto::sr25519::Public, BareCryptoStoreError> {
		let response = self.send_request(
			RequestMethod::Sr25519GenerateNew(id, seed.map(|s| s.to_string()))
		).await;
		match response {
			Ok(KeystoreResponse::Sr25519GenerateNew(result)) => result,
			_ => Err(BareCryptoStoreError::Unavailable),
		}
    }

    async fn ed25519_public_keys(&self, id: KeyTypeId) -> Vec<sp_application_crypto::ed25519::Public> {
		let response = self.send_request(RequestMethod::Ed25519PublicKeys(id)).await;
		match response {
			Ok(KeystoreResponse::Ed25519PublicKeys(keys)) => keys,
			_ => vec![],
		}
    }

    async fn ed25519_generate_new(
		&mut self,
		id: KeyTypeId,
		seed: Option<&str>,
	) -> Result<sp_application_crypto::ed25519::Public, BareCryptoStoreError> {
		let response = self.send_request(
			RequestMethod::Ed25519GenerateNew(id, seed.map(|s| s.to_string()))
		).await;
		match response {
			Ok(KeystoreResponse::Ed25519GenerateNew(result)) => result,
			_ => Err(BareCryptoStoreError::Unavailable),
		}
    }

    async fn ecdsa_public_keys(&self, id: KeyTypeId) -> Vec<sp_application_crypto::ecdsa::Public> {
		let response = self.send_request(RequestMethod::EcdsaPublicKeys(id)).await;
		match response {
			Ok(KeystoreResponse::EcdsaPublicKeys(keys)) => keys,
			_ => vec![],
		}
    }

    async fn ecdsa_generate_new(
		&mut self,
		id: KeyTypeId,
		seed: Option<&str>,
	) -> Result<sp_application_crypto::ecdsa::Public, BareCryptoStoreError> {
		let response = self.send_request(
			RequestMethod::EcdsaGenerateNew(id, seed.map(|s| s.to_string()))
		).await;
		match response {
			Ok(KeystoreResponse::EcdsaGenerateNew(result)) => result,
			_ => Err(BareCryptoStoreError::Unavailable),
		}
    }

    async fn insert_unknown(&mut self, key_type: KeyTypeId, suri: &str, public: &[u8]) -> Result<(), ()> {
		self.send_request(RequestMethod::InsertUnknown(key_type, suri.to_string(), public.to_vec())).await
			.map(|_| ())
			.map_err(|_| ())
    }

    fn password(&self) -> Option<&str> {
		None
	}

    async fn supported_keys(
		&self,
		id: KeyTypeId,
		keys: Vec<CryptoTypePublicPair>
	) -> Result<Vec<CryptoTypePublicPair>, BareCryptoStoreError> {
		let response = self.send_request(RequestMethod::SupportedKeys(id, keys)).await;
		match response {
			Ok(KeystoreResponse::SupportedKeys(keys)) => keys,
			_ => Ok(vec![])
		}
    }

    async fn keys(&self, id: KeyTypeId) -> Result<Vec<CryptoTypePublicPair>, BareCryptoStoreError> {
		let response = self.send_request(RequestMethod::Keys(id)).await;
		match response {
			Ok(KeystoreResponse::Keys(keys)) => keys,
			_ => Ok(vec![])
		}
    }

    async fn has_keys(&self, public_keys: &[(Vec<u8>, KeyTypeId)]) -> bool {
		let response = self.send_request(RequestMethod::HasKeys(public_keys.to_vec())).await;
		match response {
			Ok(KeystoreResponse::HasKeys(exists)) => exists,
			_ => false
		}
    }

    async fn sign_with(
		&self,
		id: KeyTypeId,
		key: &CryptoTypePublicPair,
		msg: &[u8],
	) -> Result<Vec<u8>, BareCryptoStoreError> {
		let response = self.send_request(RequestMethod::SignWith(id, key.clone(), msg.to_vec())).await;
		match response {
			Ok(KeystoreResponse::SignWith(result)) => result,
			_ => Err(BareCryptoStoreError::Unavailable)
		}
    }

    async fn sr25519_vrf_sign(
		&self,
		key_type: KeyTypeId,
		public: &sp_application_crypto::sr25519::Public,
		transcript_data: sp_core::vrf::VRFTranscriptData,
	) -> Result<sp_core::vrf::VRFSignature, BareCryptoStoreError> {
		let response = self.send_request(RequestMethod::Sr25519VrfSign(key_type, *public, transcript_data)).await;
		match response {
			Ok(KeystoreResponse::Sr25519VrfSign(result)) => result,
			_ => Err(BareCryptoStoreError::Unavailable)
		}
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

	fn process_request(mut store: Store, request: KeystoreRequest) -> Pin<Box<dyn Future<Output = Store> + Send>> {
		let sender = request.sender;
		match request.method {
			RequestMethod::SignWith(id, key, msg) => {
				Box::pin(async move {
					let result = store.sign_with(id, &key, &msg).await;
					let _ = sender.send(KeystoreResponse::SignWith(result));
					return store;
				})
			},
			RequestMethod::Sr25519PublicKeys(id) => {
				Box::pin(async move {
					let result = store.sr25519_public_keys(id).await;
					let _ = sender.send(KeystoreResponse::Sr25519PublicKeys(result));
					return store;
				})
			},
			RequestMethod::Sr25519VrfSign(id, public, data) => {
				Box::pin(async move {
					let result = store.sr25519_vrf_sign(id, &public, data).await;
					let _ = sender.send(KeystoreResponse::Sr25519VrfSign(result));
					return store;
				})
			},
			RequestMethod::Sr25519GenerateNew(id, seed) => {
				Box::pin(async move {
					let result = store.sr25519_generate_new(id, seed.as_deref()).await;
					let _ = sender.send(KeystoreResponse::Sr25519GenerateNew(result));
					return store;
				})
			},
			RequestMethod::Ed25519PublicKeys(id) => {
				Box::pin(async move {
					let result = store.ed25519_public_keys(id).await;
					let _ = sender.send(KeystoreResponse::Ed25519PublicKeys(result));
					return store;
				})
			},
			RequestMethod::Ed25519GenerateNew(id, seed) => {
				Box::pin(async move {
					let result = store.ed25519_generate_new(id, seed.as_deref()).await;
					let _ = sender.send(KeystoreResponse::Ed25519GenerateNew(result));
					return store;
				})
			},
			RequestMethod::EcdsaPublicKeys(id) => {
				Box::pin(async move {
					let result = store.ecdsa_public_keys(id).await;
					let _ = sender.send(KeystoreResponse::EcdsaPublicKeys(result));
					return store;
				})
			},
			RequestMethod::EcdsaGenerateNew(id, seed) => {
				Box::pin(async move {
					let result = store.ecdsa_generate_new(id, seed.as_deref()).await;
					let _ = sender.send(KeystoreResponse::EcdsaGenerateNew(result));
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
			RequestMethod::SupportedKeys(id, keys) => {
				Box::pin(async move {
					let result = store.supported_keys(id, keys).await;
					let _ = sender.send(KeystoreResponse::SupportedKeys(result));
					return store;
				})
			},
			RequestMethod::Keys(id) => {
				Box::pin(async move {
					let result = store.keys(id).await;
					let _ = sender.send(KeystoreResponse::Keys(result));
					return store;
				})
			},
			RequestMethod::Password => {
				Box::pin(async move {
					let result = store.password();
					let _ = sender.send(KeystoreResponse::Password(result.map(|s| s.to_string())));
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

pub fn adapter<Store: BareCryptoStore + 'static>(store: Store) -> (Arc<RwLock<KeystoreProxy>>, KeystoreReceiver<Store>) {
	let (keystore_proxy, keystore_receiver) = proxy(store);
	(Arc::new(RwLock::new(keystore_proxy)), keystore_receiver)
}
