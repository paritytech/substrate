#![allow(dead_code)]
#![allow(missing_docs)]
use std::{
	pin::Pin,
	task::{Context, Poll}
};
use sp_core::{
	crypto::{
		CryptoTypePublicPair,
		KeyTypeId,
	},
	ed25519,
	ecdsa,
	sr25519,
};
use sp_keystore::{
	CryptoStore, Error as CryptoStoreError,
	vrf::VRFTranscriptData,
};

use jsonrpc_core::{BoxFuture, Error as RpcError};

use futures::{
	channel::{
		oneshot,
		mpsc::{UnboundedSender, UnboundedReceiver, unbounded},
	},
	future::{Future, FutureExt, TryFutureExt},
	stream::{Stream, StreamExt},
};
use std::convert::TryInto;

use sp_consensus_babe::BABE_ENGINE_ID;

use crate::TransferableVRFTranscriptData;

impl TryInto<VRFTranscriptData> for TransferableVRFTranscriptData {
	type Error = String;

	fn try_into(self: TransferableVRFTranscriptData) -> Result<VRFTranscriptData, Self::Error> {

		let (label, field_names) = {
			if self.label.as_slice() == &BABE_ENGINE_ID {
				(&BABE_ENGINE_ID, vec!["slot number", "current epoch", "chain randomness"])
			} else {
				return Err(format!("VRF Label '{:?}' not supported", self.label))
			}
		};

		if field_names.len() != self.items.len() {
			return Err(format!("Expected '{:?}' to have {:} items but found {:}",
				label, field_names.len(), self.items.len()))
		}

		Ok(VRFTranscriptData {
			label, items: field_names.into_iter().zip(self.items).collect::<Vec<_>>()
		})
	}
}

enum State<Store: CryptoStore> {
	Idle(Store),
	Pending(Pin<Box<dyn Future<Output = Store> + Send>>),
	Ended,
}

pub struct KeystoreReceiver<Store: CryptoStore> {
	receiver: UnboundedReceiver<KeystoreRequest>,
	state: State<Store>,
}

impl<Store: CryptoStore> Unpin for KeystoreReceiver<Store> { }

impl<Store: CryptoStore + 'static> KeystoreReceiver<Store> {
	fn new(store: Store, receiver: UnboundedReceiver<KeystoreRequest>) -> Self {
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
				println!("asked for keys {:?}", id);
				Box::pin(async move {
					let result = store.keys(id).await;
					let _ = sender.send(KeystoreResponse::Keys(result));
					return store;
				})
			},
			RequestMethod::InsertUnknown(key_type, suri, pubkey) => {
				Box::pin(async move {
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

impl<Store: CryptoStore + 'static> Stream for KeystoreReceiver<Store> {
	type Item = ();

	fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
		let this = &mut *self;
		loop {
			match std::mem::replace(&mut this.state, State::Ended) {
				State::Idle(store) => {
					match Pin::new(&mut this.receiver).poll_next(cx) {
						Poll::Ready(None) => {
							return Poll::Ready(Some(()));
						},
						Poll::Ready(Some(request)) => {
							let future = KeystoreReceiver::process_request(store, request);
							this.state = State::Pending(future);
						},
						Poll::Pending => {
							this.state = State::Idle(store);
							return Poll::Pending;
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
							return Poll::Pending;
						}
					}
				},
				State::Ended => {
					return Poll::Ready(None);
				}
			}
		}
	}
}


enum RequestMethod {
	Sr25519PublicKeys(KeyTypeId),
	Sr25519GenerateNew(KeyTypeId, Option<String>),
	Sr25519VrfSign(
		KeyTypeId,
		sp_application_crypto::sr25519::Public,
		sp_keystore::vrf::VRFTranscriptData,
	),
	Ed25519PublicKeys(KeyTypeId),
	Ed25519GenerateNew(KeyTypeId, Option<String>),
	EcdsaPublicKeys(KeyTypeId),
	EcdsaGenerateNew(KeyTypeId, Option<String>),
	InsertUnknown(KeyTypeId, String, Vec<u8>),
	SupportedKeys(KeyTypeId, Vec<CryptoTypePublicPair>),
	Keys(KeyTypeId,),
	HasKeys(Vec<(Vec<u8>, KeyTypeId)>),
	SignWith(KeyTypeId, CryptoTypePublicPair, Vec<u8>),
}

struct KeystoreRequest {
	sender: oneshot::Sender<KeystoreResponse>,
	method: RequestMethod,
}

enum KeystoreResponse {
	Sr25519PublicKeys(Vec<sr25519::Public>),
	Sr25519GenerateNew(
		Result<sp_application_crypto::sr25519::Public, CryptoStoreError>
	),
	Sr25519VrfSign(
		Result<sp_keystore::vrf::VRFSignature, CryptoStoreError>
	),
	Ed25519PublicKeys(Vec<ed25519::Public>),
	Ed25519GenerateNew(
		Result<sp_application_crypto::ed25519::Public, CryptoStoreError>
	),
	EcdsaPublicKeys(Vec<ecdsa::Public>),
	EcdsaGenerateNew(
		Result<sp_application_crypto::ecdsa::Public, CryptoStoreError>
	),
	InsertUnknown(Result<(), ()>),
	SupportedKeys(Result<Vec<CryptoTypePublicPair>, CryptoStoreError>),
	Keys(Result<Vec<CryptoTypePublicPair>, CryptoStoreError>),
	HasKeys(bool),
	SignWith(Result<Vec<u8>, CryptoStoreError>),
}



pub struct GenericRemoteSignerServer{
	sender: UnboundedSender<KeystoreRequest>,
}

impl GenericRemoteSignerServer {

	pub fn proxy<Store: CryptoStore + 'static>(store: Store) -> (Self, KeystoreReceiver<Store>) {
		let (sender, receiver) = unbounded::<KeystoreRequest>();
		(GenericRemoteSignerServer { sender }, KeystoreReceiver::new(store, receiver))
	}


	fn send_request(
		&self,
		request: RequestMethod
	) ->  oneshot::Receiver<KeystoreResponse> {
		let (request_sender, receiver) = oneshot::channel::<KeystoreResponse>();

		let request = KeystoreRequest {
			sender: request_sender,
			method: request,
		};
		self.sender.unbounded_send(request).expect("Unbounded Send doesn't fail");
		receiver
	}
}

impl crate::RemoteSignerApi for GenericRemoteSignerServer {

	fn sr25519_public_keys(&self, id: KeyTypeId) -> BoxFuture<Vec<sr25519::Public>> {
		let receiver = self.send_request(RequestMethod::Sr25519PublicKeys(id));
		Box::new(receiver.map(|e| match e {
			Ok(KeystoreResponse::Sr25519PublicKeys(keys)) => Ok(keys),
			_ => Ok(vec![]),
		}).boxed().compat())
	}


    fn sr25519_generate_new(
		&self,
		id: KeyTypeId,
		seed: Option<String>,
	) -> BoxFuture<sp_application_crypto::sr25519::Public> {
		Box::new(self.send_request(
			RequestMethod::Sr25519GenerateNew(id, seed)
		).map(|response|
			if  let Ok(KeystoreResponse::Sr25519GenerateNew(result)) = response {
				 result.map_err(|_|RpcError::internal_error())
			} else {
				Err(RpcError::internal_error())
			}
		).boxed().compat())
    }

	fn ed25519_public_keys(&self, id: KeyTypeId)
		-> BoxFuture<Vec<sp_application_crypto::ed25519::Public>>
	{
		Box::new(self.send_request(RequestMethod::Ed25519PublicKeys(id)).map(|response|
			if let Ok(KeystoreResponse::Ed25519PublicKeys(keys)) = response {
				Ok(keys)
			} else {
				Ok(vec![])
			}
		).boxed().compat())
    }

    fn ed25519_generate_new(
		&self,
		id: KeyTypeId,
		seed: Option<String>,
	) -> BoxFuture<sp_application_crypto::ed25519::Public> {
		Box::new(self.send_request(
			RequestMethod::Ed25519GenerateNew(id, seed)
		).map(|response|
			if let Ok(KeystoreResponse::Ed25519GenerateNew(result)) = response {
				result.map_err(|_| RpcError::internal_error())
			} else {
				Err(RpcError::internal_error())
			}
		).boxed().compat())
    }

	fn ecdsa_public_keys(&self, id: KeyTypeId)
		-> BoxFuture<Vec<sp_application_crypto::ecdsa::Public>>
	{
		Box::new(self.send_request(RequestMethod::EcdsaPublicKeys(id)).map(|response|
			if let Ok(KeystoreResponse::EcdsaPublicKeys(keys)) = response
			{
				Ok(keys)
			} else {
				Ok(vec![])
			}
		).boxed().compat())
    }

    fn ecdsa_generate_new(
		&self,
		id: KeyTypeId,
		seed: Option<String>,
	) -> BoxFuture<sp_application_crypto::ecdsa::Public> {
		Box::new(self.send_request(
			RequestMethod::EcdsaGenerateNew(id, seed)
		).map(|response|
			if let Ok(KeystoreResponse::EcdsaGenerateNew(result)) = response
				 {
				result.map_err(|_| RpcError::internal_error())
			} else {
				Err(RpcError::internal_error())
			}
		).boxed().compat())
    }

    fn insert_unknown(&self, key_type: KeyTypeId, suri: String, public: Vec<u8>) -> BoxFuture<()> {
		Box::new(
			self.send_request(RequestMethod::InsertUnknown(
					key_type, suri, public)
			).map(|_| Ok(())).boxed().compat())
	}

    fn supported_keys(
		&self,
		id: KeyTypeId,
		keys: Vec<CryptoTypePublicPair>
	) -> BoxFuture<Vec<CryptoTypePublicPair>> {
		Box::new(self.send_request(RequestMethod::SupportedKeys(id, keys)).map(|response|
			if let Ok(KeystoreResponse::SupportedKeys(keys)) = response {
				keys.map_err(|_| RpcError::internal_error())
			} else {
				Ok(vec![])
			}
		).boxed().compat())
    }

    fn keys(&self, id: KeyTypeId) -> BoxFuture<Vec<CryptoTypePublicPair>> {
		Box::new(self.send_request(RequestMethod::Keys(id)).map(|response|
			if let Ok(KeystoreResponse::Keys(keys)) = response {
				keys.map_err(|_| RpcError::internal_error())
			} else {
				Ok(vec![])
			}
		).boxed().compat())
    }

    fn has_keys(&self, public_keys: Vec<(Vec<u8>, KeyTypeId)>) -> BoxFuture<bool> {
		Box::new(self.send_request(RequestMethod::HasKeys(public_keys.to_vec())).map(|response|
			if let Ok(KeystoreResponse::HasKeys(exists)) = response {
				Ok(exists)
			} else {
				Ok(false)
			}
		).boxed().compat())
    }

    fn sign_with(
		&self,
		id: KeyTypeId,
		key: CryptoTypePublicPair,
		msg: Vec<u8>,
	) -> BoxFuture<Vec<u8>> {
		Box::new(self.send_request(RequestMethod::SignWith(id, key, msg)).map(|response|
			if let Ok(KeystoreResponse::SignWith(result)) =  response {
				result.map_err(|_| RpcError::internal_error())
			} else {
				Err(RpcError::internal_error())
			}
		).boxed().compat())
	}

	fn sign_with_any(
		&self,
		id: KeyTypeId,
		keys: Vec<CryptoTypePublicPair>,
		msg: Vec<u8>
	) -> BoxFuture<(CryptoTypePublicPair, Vec<u8>)> {
		todo!{}
	}

	fn sign_with_all(
		&self,
		id: KeyTypeId,
		keys: Vec<CryptoTypePublicPair>,
		msg: Vec<u8>,
	) -> BoxFuture<Vec<Result<Vec<u8>, String>>> {
		todo!{}
	}

    fn sr25519_vrf_sign(
		&self,
		key_type: KeyTypeId,
		public: sp_application_crypto::sr25519::Public,
		transcript_data: crate::TransferableVRFTranscriptData,
	) -> BoxFuture<sp_keystore::vrf::VRFSignature> {

		match transcript_data.try_into() {
			Ok(vrf_data) =>  Box::new(
				self.send_request(RequestMethod::Sr25519VrfSign(key_type, public, vrf_data))
					.map(|response|
						if let Ok(KeystoreResponse::Sr25519VrfSign(result)) = response {
							result.map_err(|_| RpcError::internal_error())
						} else {
							Err(RpcError::internal_error())
						}
					).boxed()
				.compat()
			),
			Err(e) => Box::new(futures::future::err(RpcError::invalid_params(e)).compat())
		}
    }
}

#[cfg(test)]
mod tests {
	use tokio;
	use serde_json;
	use sp_core::traits::CryptoStore;
	use jsonrpc_test;
	use sc_keystore::LocalKeystore;

	use super::*;
	use crate::RemoteSignerApi;

	const TEST_TK : KeyTypeId = KeyTypeId(*b"test");
	const TEST_TK_NOPE : KeyTypeId = KeyTypeId(*b"nope");

	async fn setup(msg_count: u8) -> jsonrpc_test::Rpc {
		let keystore = LocalKeystore::in_memory();
		keystore.sr25519_generate_new(TEST_TK, Some("//Alice"))
			.await.expect("InMem Keystore doesn't fail");
		keystore.ed25519_generate_new(TEST_TK, Some("//Bob"))
			.await.expect("InMem Keystore doesn't fail");
		keystore.ecdsa_generate_new(TEST_TK, Some("//Charlie"))
			.await.expect("InMem Keystore doesn't fail");


		let (server, mut runner) = GenericRemoteSignerServer::proxy(keystore);

		tokio::task::spawn(async move {
			for _ in 0..msg_count {
				runner.next().await;
			}
		});

		jsonrpc_test::Rpc::new(RemoteSignerApi::to_delegate(server))
	}

	#[tokio::test(core_threads=4)]
	async fn test_keys() {
		let rpc = setup(2).await;
		let r = rpc.request("signer_keys", &[TEST_TK]);
		let res : Vec<CryptoTypePublicPair> = serde_json::from_str(&r).unwrap();
		assert_eq!(res.len(), 9);

		let r = rpc.request("signer_keys", &[TEST_TK_NOPE]);
		let res : Vec<CryptoTypePublicPair> = serde_json::from_str(&r).unwrap();
		assert_eq!(res.len(), 0);
	}

	#[tokio::test(core_threads=4)]
	async fn test_sr25519_public_keys() {
		let rpc = setup(2).await;
		let r = rpc.request("signer_sr25519_public_keys", &[TEST_TK]);
		let res : Vec<sr25519::Public> = serde_json::from_str(&r).unwrap();
		assert_eq!(res.len(), 3);

		let r = rpc.request("signer_sr25519_public_keys", &[TEST_TK_NOPE]);
		let res : Vec<sr25519::Public> = serde_json::from_str(&r).unwrap();
		assert_eq!(res.len(), 0);
	}

	#[tokio::test(core_threads=4)]
	async fn test_ed25519_public_keys() {
		let rpc = setup(2).await;
		let r = rpc.request("signer_ed25519_public_keys", &[TEST_TK]);
		let res : Vec<ed25519::Public> = serde_json::from_str(&r).unwrap();
		assert_eq!(res.len(), 3);

		let r = rpc.request("signer_ed25519_public_keys", &[TEST_TK_NOPE]);
		let res : Vec<ed25519::Public> = serde_json::from_str(&r).unwrap();
		assert_eq!(res.len(), 0);
	}

	#[tokio::test(core_threads=4)]
	async fn test_ecdsa_public_keys() {
		let rpc = setup(2).await;
		let r = rpc.request("signer_ecdsa_public_keys", &[TEST_TK]);
		let res : Vec<ecdsa::Public> = serde_json::from_str(&r).unwrap();
		assert_eq!(res.len(), 2);

		let r = rpc.request("signer_ecdsa_public_keys", &[TEST_TK_NOPE]);
		let res : Vec<ecdsa::Public> = serde_json::from_str(&r).unwrap();
		assert_eq!(res.len(), 0);
	}
}