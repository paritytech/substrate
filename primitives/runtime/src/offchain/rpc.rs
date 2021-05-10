// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! A high-level helpers for making RPC calls from Offchain Workers.

use serde::{Deserialize, Deserializer};
use crate::{RuntimeDebug, offchain::Duration};
use serde_json::json;
use sp_std::{vec::Vec, str};
use super::http;

/// A rpc call error
#[derive(Clone, PartialEq, Eq, RuntimeDebug)]
pub enum Error {
	/// Response can not be deserialized
	Deserializing,
	/// Http error
	Http(http::Error)
}

/// A rpc result type
pub type RpcResult = Result<Response, Error>;

/// A rpc call error field
#[derive(Deserialize, Default, RuntimeDebug)]
pub struct RpcError {
	/// error code
	pub code: i32,
	/// error message
	#[serde(deserialize_with = "de_string_to_bytes")]
	pub message: Vec<u8>
}

/// A rpc call response
#[derive(Deserialize, Default, RuntimeDebug)]
pub struct Response {
	/// rpc response jsonrpc
	#[serde(deserialize_with = "de_string_to_bytes")]
	pub jsonrpc: Vec<u8>,
	/// rpc response result
	#[serde(default)]
	#[serde(deserialize_with = "de_string_to_bytes")]
	pub result: Vec<u8>,
	/// rpc response error struct
	#[serde(default)]
	pub error: RpcError,
	/// rpc response id
	pub id: u32
}

/// A rpc call request
pub struct Request<'a> {
	/// rpc request jsonrpc
	pub jsonrpc: &'a str,
	/// rpc request id
	pub id: u32,
	/// rpc request method
	pub method: &'a str,
	/// rpc request params
	pub params: Vec<&'a str>,
	/// rpc request timeout
	pub timeout: u64,
	/// rpc request url
	pub url: &'a str
}

fn de_string_to_bytes<'de, D>(de: D) -> Result<Vec<u8>, D::Error>
where
	D: Deserializer<'de>,
{
	let s: &str = Deserialize::deserialize(de)?;
	Ok(s.as_bytes().to_vec())
}

impl<'a> Request<'a> {
	/// Send the request and return a Rpc result.
	///
	/// Err is returned in case there is a Http
	/// or deserialize error.
	pub fn send(&self) -> RpcResult {
		let request_body = json!({
			"jsonrpc": self.jsonrpc,
			"id": self.id,
			"method": self.method,
			"params": self.params
		});

		let mut body: Vec<&[u8]> = Vec::new();
		let request_body_slice: &[u8] = &(serde_json::to_vec(&request_body).unwrap())[..];
		body.push(request_body_slice);

		let post_request = http::Request::post(self.url, body);

		let timeout = sp_io::offchain::timestamp().add(Duration::from_millis(self.timeout));

		let pending = match post_request
			.add_header("Content-Type", "application/json;charset=utf-8")
			.deadline(timeout)
			.send().map_err(|_| http::Error::IoError) {
				Ok(result) => result,
				Err(e) => return Err(Error::Http(e)),
		};

		let response = match pending.try_wait(timeout).map_err(|_| http::Error::DeadlineReached) {
			Ok(result) =>
				match result {
					Ok(result_bis) => result_bis,
					Err(e) => return Err(Error::Http(e)),
				},
			Err(e) => return Err(Error::Http(e)),
		};

		if response.code != 200 {
			log::warn!("Unexpected status code: {}", response.code);
			return Err(Error::Http(http::Error::Unknown));
		}

		let response_body_bytes = response.body().collect::<Vec<u8>>();
		let rpc_response: Response = serde_json::from_slice(&response_body_bytes).map_err(|_| Error::Deserializing)?;

		Ok(rpc_response)
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use std::sync::Arc;
	// use sp_core::H256;
	use substrate_test_runtime_client::{
		prelude::*,
		sp_consensus::BlockOrigin,
		runtime::{H256, Block, Header},
	};
	use jsonrpc_pubsub::{manager::SubscriptionManager};
	// use crate::testing::TaskExecutor;
	use sc_rpc::{chain::{new_full, ChainApi}, testing::TaskExecutor};

	use sp_io::TestExternalities;
	use sp_core::offchain::{
		OffchainWorkerExt,
		testing,
	};

	#[test]
	fn should_return_rpc_response() {
		let mut client = Arc::new(substrate_test_runtime_client::new());
		let api = new_full(client.clone(), SubscriptionManager::new(Arc::new(TaskExecutor)));

		let (offchain, state) = testing::TestOffchainExt::new();
		let mut t = TestExternalities::default();
		t.register_extension(OffchainWorkerExt::new(offchain));

		// const RPC_REQUEST_URL: &str = "http://localhost:9933";
		const RPC_REQUEST_URL: &str = "http://localhost:9933";
		const TIMEOUT_PERIOD: u64 = 3_000;
		// const JSONRPC: &str = "2.0";
		const RPC_METHOD: &str = "chain_getFinalizedHead";
		const EXPECTED_RESULT: &[u8] = b"0x3141e6406e195803b0f367c4c6aacc0673a5432f3ec010afae602ff09998123b";

		let request_body = json!({
			"jsonrpc": "2.0",
			"id": 1,
			"method": RPC_METHOD,
			"params": Vec::<&str>::new()
		});

		let mut body: Vec<&[u8]> = Vec::new();
		let request_body_slice: &[u8] = &(serde_json::to_vec(&request_body).unwrap())[..];

		{
			let mut state = state.write();

			state.expect_request(testing::PendingRequest {
				method: "POST".into(),
				uri: RPC_REQUEST_URL.into(),
				body: request_body_slice.to_vec(),
				headers: vec![("Content-Type".to_string(), "application/json;charset=utf-8".to_string())],
				response: Some(br#"{"jsonrpc":"2.0","result":"0x3141e6406e195803b0f367c4c6aacc0673a5432f3ec010afae602ff09998123b","id":1}"#.to_vec()),
				sent: true,
				..Default::default()
			});
		}

		t.execute_with(|| {


			// let pending = http::Request::default()
			// 	.method(http::Method::Post)
			// 	.url("http://localhost:1234")
			// 	.body(vec![request_body_slice])
			// 	.send()
			// 	.unwrap();

			// state.write().fulfill_pending_request(
			// 	1,
			// 	testing::PendingRequest {
			// 		method: "POST".into(),
			// 		uri: RPC_REQUEST_URL.into(),
			// 		body: request_body_slice.to_vec(),
			// 		sent: true,
			// 		..Default::default()
			// 	},
			// 	request_body_slice.to_vec(),
			// 	None,
			// );

			let request = Request {
				jsonrpc: "2.0",
				id: 1,
				method: RPC_METHOD,
				params: Vec::new(),
				timeout: TIMEOUT_PERIOD,
				url: RPC_REQUEST_URL
			};

			let rpc_response = request.send();

			match rpc_response {
				Ok(response) => {
					if !response.result.is_empty() {
						// log::info!("Rpc call result: {:?}", str::from_utf8(&response.result).unwrap());
						let finalized_hash_str = str::from_utf8(&response.result[2..]).unwrap();
						let finalized_hash = hex::decode(finalized_hash_str).ok().unwrap();

						let expected_finalized_hash_str = str::from_utf8(&EXPECTED_RESULT[2..]).unwrap();
						let expected_finalized_hash = hex::decode(expected_finalized_hash_str).ok().unwrap();

						assert_eq!(
							H256::from_slice(&expected_finalized_hash[0..32]),
							H256::from_slice(&finalized_hash[0..32])
						);
					} else {
						log::error!("Rpc call error: code: {:?}, message: {:?}",
										response.error.code,
										str::from_utf8(&response.error.message).unwrap()
									);
					}
				},
				Err(e) => {
					log::error!("Rpc call error: {:?}", e);
				}
			}
		})

		// log::debug!("=============== TEST ================= {:?}", api.finalized_head());

		// let finalized_hash = b"01a925bd4e798b3e6e28351cbe02facd5fbdb0bc5e92bd19bf061f4344edac02";

	}
}
