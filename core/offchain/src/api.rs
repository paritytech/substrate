// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use std::sync::Arc;
use futures::{Stream, Future, sync::mpsc};
use log::{info, debug, warn, error};
use parity_codec::Decode;
use primitives::offchain::{
	Timestamp, HttpRequestId, HttpRequestStatus, HttpError,
	Externalities as OffchainExt,
	CryptoKind, CryptoKeyId,
};
use runtime_primitives::{
	generic::BlockId,
	traits::{self, Extrinsic},
};
use transaction_pool::txpool::{Pool, ChainApi};

/// A message between the offchain extension and the processing thread.
enum ExtMessage {
	SubmitExtrinsic(Vec<u8>),
}

/// Asynchronous offchain API.
///
/// NOTE this is done to prevent recursive calls into the runtime (which are not supported currently).
pub(crate) struct Api {
	sender: mpsc::UnboundedSender<ExtMessage>,
	db: client_db::offchain::LocalStorage,
}

fn unavailable_yet<R: Default>(name: &str) -> R {
	error!("The {:?} API is not available for offchain workers yet. Follow \
		   https://github.com/paritytech/substrate/issues/1458 for details", name);
	Default::default()
}

impl OffchainExt for Api {
	fn submit_transaction(&mut self, ext: Vec<u8>) -> Result<(), ()> {
		self.sender
			.unbounded_send(ExtMessage::SubmitExtrinsic(ext))
			.map(|_| ())
			.map_err(|_| ())
	}

	fn new_crypto_key(&mut self, _crypto: CryptoKind) -> Result<CryptoKeyId, ()> {
		unavailable_yet::<()>("new_crypto_key");
		Err(())
	}

	fn encrypt(&mut self, _key: Option<CryptoKeyId>, _data: &[u8]) -> Result<Vec<u8>, ()> {
		unavailable_yet::<()>("encrypt");
		Err(())
	}

	fn decrypt(&mut self, _key: Option<CryptoKeyId>, _data: &[u8]) -> Result<Vec<u8>, ()> {
		unavailable_yet::<()>("decrypt");
		Err(())
	}

	fn sign(&mut self, _key: Option<CryptoKeyId>, _data: &[u8]) -> Result<Vec<u8>, ()> {
		unavailable_yet::<()>("sign");
		Err(())
	}

	fn verify(&mut self, _key: Option<CryptoKeyId>, _msg: &[u8], _signature: &[u8]) -> Result<bool, ()> {
		unavailable_yet::<()>("verify");
		Err(())
	}

	fn timestamp(&mut self) -> Timestamp {
		unavailable_yet("timestamp")
	}

	fn sleep_until(&mut self, _deadline: Timestamp) {
		unavailable_yet::<()>("sleep_until")
	}

	fn random_seed(&mut self) -> [u8; 32] {
		unavailable_yet("random_seed")
	}

	fn local_storage_set(&mut self, _key: &[u8], _value: &[u8]) {
		unavailable_yet("local_storage_set")
	}

	fn local_storage_compare_and_set(&mut self, _key: &[u8], _old_value: &[u8], _new_value: &[u8]) {
		unavailable_yet("local_storage_compare_and_set")
	}

	fn local_storage_get(&mut self, _key: &[u8]) -> Option<Vec<u8>> {
		unavailable_yet("local_storage_get")
	}

	fn http_request_start(
		&mut self,
		_method: &str,
		_uri: &str,
		_meta: &[u8]
	) -> Result<HttpRequestId, ()> {
		unavailable_yet::<()>("http_request_start");
		Err(())
	}

	fn http_request_add_header(
		&mut self,
		_request_id: HttpRequestId,
		_name: &str,
		_value: &str
	) -> Result<(), ()> {
		unavailable_yet::<()>("http_request_add_header");
		Err(())
	}

	fn http_request_write_body(
		&mut self,
		_request_id: HttpRequestId,
		_chunk: &[u8],
		_deadline: Option<Timestamp>
	) -> Result<(), HttpError> {
		unavailable_yet::<()>("http_request_write_body");
		Err(HttpError::IoError)
	}

	fn http_response_wait(
		&mut self,
		ids: &[HttpRequestId],
		_deadline: Option<Timestamp>
	) -> Vec<HttpRequestStatus> {
		unavailable_yet::<()>("http_response_wait");
		ids.iter().map(|_| HttpRequestStatus::Unknown).collect()
	}

	fn http_response_headers(
		&mut self,
		_request_id: HttpRequestId
	) -> Vec<(Vec<u8>, Vec<u8>)> {
		unavailable_yet("http_response_headers")
	}

	fn http_response_read_body(
		&mut self,
		_request_id: HttpRequestId,
		_buffer: &mut [u8],
		_deadline: Option<Timestamp>
	) -> Result<usize, HttpError> {
		unavailable_yet::<()>("http_response_read_body");
		Err(HttpError::IoError)
	}
}

/// Offchain extensions implementation API
///
/// This is the asynchronous processing part of the API.
pub(crate) struct AsyncApi<A: ChainApi> {
	receiver: Option<mpsc::UnboundedReceiver<ExtMessage>>,
	transaction_pool: Arc<Pool<A>>,
	at: BlockId<A::Block>,
}

impl<A: ChainApi> AsyncApi<A> {
	/// Creates new Offchain extensions API implementation  an the asynchronous processing part.
	pub fn new(
		transaction_pool: Arc<Pool<A>>,
		db: client_db::offchain::LocalStorage,
		at: BlockId<A::Block>,
	) -> (Api, AsyncApi<A>) {
		let (sender, rx) = mpsc::unbounded();

		let api = Api {
			sender,
			db,
		};

		let async_api = AsyncApi {
			receiver: Some(rx),
			transaction_pool,
			at,
		};

		(api, async_api)
	}

	/// Run a processing task for the API
	pub fn process(mut self) -> impl Future<Item=(), Error=()> {
		let receiver = self.receiver.take().expect("Take invoked only once.");

		receiver.for_each(move |msg| {
			match msg {
				ExtMessage::SubmitExtrinsic(ext) => self.submit_extrinsic(ext),
			}
			Ok(())
		})
	}

	fn submit_extrinsic(&mut self, ext: Vec<u8>) {
		let xt = match <A::Block as traits::Block>::Extrinsic::decode(&mut &*ext) {
			Some(xt) => xt,
			None => {
				warn!("Unable to decode extrinsic: {:?}", ext);
				return
			},
		};

		info!("Submitting to the pool: {:?} (isSigned: {:?})", xt, xt.is_signed());
		match self.transaction_pool.submit_one(&self.at, xt.clone()) {
			Ok(hash) => debug!("[{:?}] Offchain transaction added to the pool.", hash),
			Err(e) => {
				debug!("Couldn't submit transaction: {:?}", e);
			},
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	fn offchain_api() -> (AsyncApi, Api<impl ChainApi>) {
		let _ = env_logger::try_init();
		let client = Arc::new(test_client::new());
		let pool = Arc::new(Pool::new(Default::default(), transaction_pool::ChainApi::new(client.clone())));

		Api::new(pool, BlockId::Number(0))
	}

	#[test]
	fn should_set_and_get_local_storage() {
		// given
		let mut api = offchain_api().0;
		let key = b"test";

		// when
		assert_eq!(api.local_storage_get(key), None);
		api.local_storage_set(key, b"value");

		// then
		assert_eq!(api.local_storage_get(key), Some(b"value".to_vec()));

		// then
	}
}
