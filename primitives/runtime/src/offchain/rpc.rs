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
//!
//! Example:
// ! ```rust,no_run
// ! use sp_runtime::offchain::rpc::{Request, Error};
// ! use sp_runtime::offchain::http;
// ! use sp_std::{vec::Vec, str};
// !
// ! let request = Request {
// ! 	jsonrpc: "2.0",
// ! 	id: 1,
// ! 	method: "chain_getFinalizedHead",
// ! 	params: Vec::new(),
// ! 	timeout: 3_000,
// ! 	url: "http://localhost:9933"
// ! };
// !
// ! let rpc_response = request.send();
// !
// ! match rpc_response {
// ! 	Ok(response) => {
// ! 		if !response.result.is_empty() {
// ! 			log::info!("Rpc call result: {:?}", str::from_utf8(&response.result).unwrap());
// ! 		} else {
// ! 			log::error!("Rpc call error: code: {:?}, message: {:?}",
// ! 							response.error.code,
// ! 							str::from_utf8(&response.error.message).unwrap()
// ! 						);
// ! 		}
// ! 	},
// ! 	Err(e) => {
// ! 		log::error!("Rpc call error: {:?}", e);
// ! 		assert_eq!(Error::Http(http::Error::DeadlineReached), e);
// ! 	}
// ! }
// ! ```

use serde::{Deserialize, Deserializer};
use crate::{RuntimeDebug, offchain::Duration};
use serde_json::{json, Value};
use sp_std::{vec::Vec, str};
use super::http;

/// A rpc call error
#[derive(Clone, PartialEq, Eq, RuntimeDebug)]
pub enum Error {
	/// Response can not be deserialized
	Deserializing,
	/// Http error
	Http(http::Error),
}

/// A rpc result type
pub type RpcResult = Result<Response, Error>;

/// A rpc call error field
#[derive(RuntimeDebug, PartialEq)]
pub struct RpcError {
	/// error code
	pub code: i32,
	/// error message
	pub message: Vec<u8>,
	/// error data
	pub data: Option<Value>,
}

/// A rpc call response
#[derive(RuntimeDebug, PartialEq)]
pub struct Response {
	/// rpc response jsonrpc
	pub jsonrpc: Vec<u8>,
	/// rpc response result
	pub result: Option<Value>,
	/// rpc response error struct
	pub error: Option<RpcError>,
	/// rpc response id
	pub id: u32,
}

/// A rpc call request
#[derive(RuntimeDebug)]
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
	pub url: &'a str,
}

impl<'a> Default for Request<'a> {
	fn default() -> Self {
		Request {
			jsonrpc: "2.0",
			id: 1,
			method: "chain_getFinalizedHead",
			params: Vec::new(),
			timeout: 3_000,
			url: "http://localhost:9933"
		}
	}
}

fn de_option_string_to_bytes<'de, D>(de: D) -> Result<Option<Vec<u8>>, D::Error>
where
	D: Deserializer<'de>,
{
	let s: Option<&str> = Deserialize::deserialize(de)?;

	match s {
		Some(value) => Ok(Some(value.as_bytes().to_vec())),
		None => Ok(None),
	}
}

fn de_string_to_bytes<'de, D>(de: D) -> Result<Vec<u8>, D::Error>
where
	D: Deserializer<'de>,
{
	let s: &str = Deserialize::deserialize(de)?;
	Ok(s.as_bytes().to_vec())
}

impl<'a> Request<'a> {
	/// Send the request and return a RPC result.
	///
	/// Err is returned in case there is a Http
	/// or deserializing error.
	pub fn send(&self) -> RpcResult {
		// Construct http POST body
		let request_body = json!({
			"jsonrpc": self.jsonrpc,
			"id": self.id,
			"method": self.method,
			"params": self.params
		});
		let mut body: Vec<&[u8]> = Vec::new();
		let request_body_slice: &[u8] = &(serde_json::to_vec(&request_body).unwrap())[..];
		body.push(request_body_slice);

		// Send http POST request
		let post_request = http::Request::post(self.url, body);
		let timeout = sp_io::offchain::timestamp().add(Duration::from_millis(self.timeout));
		let pending = match post_request
			.add_header("Content-Type", "application/json;charset=utf-8")
			.deadline(timeout)
			.send().map_err(|_| http::Error::IoError) {
				Ok(result) => result,
				Err(e) => return Err(Error::Http(e)),
		};

		// Hanlde http response
		let response = match pending.try_wait(timeout)
			.map_err(|_| http::Error::DeadlineReached) {
				Ok(result) =>
					match result {
						Ok(result_bis) => result_bis,
						Err(e) => return Err(Error::Http(e)),
					},
				Err(e) => return Err(Error::Http(e)),
		};

		// Return http error if response status is not 200
		if response.code != 200 {
			log::warn!("Unexpected status code: {}", response.code);
			return Err(Error::Http(http::Error::Unknown));
		}

		// Deserialize response body
		let response_body_bytes = response.body().collect::<Vec<u8>>();
		let rpc_result = Self::deserialize_response(&response_body_bytes)?;

		Ok(rpc_result)
	}

	fn deserialize_response(response_body_bytes: &Vec<u8>) -> RpcResult {
		let response_deserialized: Value = serde_json::from_slice(response_body_bytes)
			.map_err(|_| Error::Deserializing)?;

		response_deserialized.as_object().ok_or(Error::Deserializing)?;

		let jsonrpc_value = response_deserialized.get("jsonrpc").ok_or(Error::Deserializing)?;
		let jsonrpc = jsonrpc_value.as_str().ok_or(Error::Deserializing)?;

		let id_value = response_deserialized.get("id").ok_or(Error::Deserializing)?;
		let id = id_value.as_u64().ok_or(Error::Deserializing)?;

		let result_value = response_deserialized.get("result");
		let error_value = response_deserialized.get("error");

		let error: Option<RpcError> = match error_value {
			Some(value) => {
				let code_value = value.get("code").ok_or(Error::Deserializing)?;
				let code = code_value.as_i64().ok_or(Error::Deserializing)?;
				let message_value = value.get("message").ok_or(Error::Deserializing)?;
				let message = message_value.as_str().ok_or(Error::Deserializing)?;
				let data_value = value.get("data");

				let rpc_error = RpcError {
					code: code as i32,
					message: message.as_bytes().to_vec(),
					data: data_value.cloned()
				};
				Some(rpc_error)
			},
			None => None
		};

		let rpc_response = Response {
			jsonrpc: jsonrpc.as_bytes().to_vec(),
			result: result_value.cloned(),
			error,
			id: id as u32,
		};

		Ok(rpc_response)
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use sp_io::TestExternalities;
	use sp_core::{offchain::{OffchainWorkerExt, testing}, H256};

	const RPC_REQUEST_URL: &'static str = "http://localhost:9933";
	const TIMEOUT_PERIOD: u64 = 3_000;

	#[test]
	fn should_return_rpc_result() {
		let (offchain, state) = testing::TestOffchainExt::new();
		let mut t = TestExternalities::default();
		t.register_extension(OffchainWorkerExt::new(offchain));

		const RPC_METHOD: &'static str = "chain_getFinalizedHead";
		const RESPONSE: &[u8] =
			br#"{"jsonrpc":"2.0","result":"0x3141e6406e195803b0f367c4c6aacc0673a5432f3ec010afae602ff09998123b","id":1}"#;
		const EXPECTED_RESULT: &[u8] = b"0x3141e6406e195803b0f367c4c6aacc0673a5432f3ec010afae602ff09998123b";

		let request_body = json!({
			"jsonrpc": "2.0",
			"id": 1,
			"method": RPC_METHOD,
			"params": Vec::<&str>::new()
		});

		let request_body_slice: &[u8] = &(serde_json::to_vec(&request_body).unwrap())[..];

		{
			let mut state = state.write();

			state.expect_request(testing::PendingRequest {
				method: "POST".into(),
				uri: RPC_REQUEST_URL.into(),
				body: request_body_slice.to_vec(),
				headers: vec![(
					"Content-Type".to_string(),
					"application/json;charset=utf-8".to_string()
				)],
				response: Some(RESPONSE.to_vec()),
				sent: true,
				..Default::default()
			});
		}

		t.execute_with(|| {
			let request = Request {
				..Default::default()
			};

			let response = request.send().unwrap();

			let expected_response = Response {
				jsonrpc: b"2.0".to_vec(),
				result: Some(json!(str::from_utf8(EXPECTED_RESULT).unwrap())),
				error: None,
				id: 1,
			};

			assert_eq!(expected_response, response);
		})
	}

	// #[test]
	// fn should_return_rpc_error() {
	// 	let (offchain, state) = testing::TestOffchainExt::new();
	// 	let mut t = TestExternalities::default();
	// 	t.register_extension(OffchainWorkerExt::new(offchain));

	// 	const RPC_METHOD: &'static str = "chain_madeUpMethod";
	// 	const RESPONSE: &[u8] = br#"{"jsonrpc":"2.0","error":{"code":-32601,"message":"Method not found"},"id":1}"#;
	// 	const EXPECTED_ERROR_CODE: i32 = -32601;
	// 	const EXPECTED_ERROR_MESSAGE: &[u8] = b"Method not found";

	// 	let request_body = json!({
	// 		"jsonrpc": "2.0",
	// 		"id": 1,
	// 		"method": RPC_METHOD,
	// 		"params": Vec::<&str>::new()
	// 	});

	// 	let request_body_slice: &[u8] = &(serde_json::to_vec(&request_body).unwrap())[..];

	// 	{
	// 		let mut state = state.write();

	// 		state.expect_request(testing::PendingRequest {
	// 			method: "POST".into(),
	// 			uri: RPC_REQUEST_URL.into(),
	// 			body: request_body_slice.to_vec(),
	// 			headers: vec![(
	// 				"Content-Type".to_string(),
	// 				"application/json;charset=utf-8".to_string()
	// 			)],
	// 			response: Some(RESPONSE.to_vec()),
	// 			sent: true,
	// 			..Default::default()
	// 		});
	// 	}

	// 	t.execute_with(|| {
	// 		let request = Request {
	// 			method: RPC_METHOD,
	// 			..Default::default()
	// 		};

	// 		let error = request.send().unwrap().error.unwrap();
	// 		assert_eq!(EXPECTED_ERROR_CODE, error.code);
	// 		assert_eq!(EXPECTED_ERROR_MESSAGE, &error.message[..]);
	// 	})
	// }

	// #[test]
	// fn should_return_deserializing_error() {
	// 	let (offchain, state) = testing::TestOffchainExt::new();
	// 	let mut t = TestExternalities::default();
	// 	t.register_extension(OffchainWorkerExt::new(offchain));

	// 	const RPC_METHOD: &'static str = "chain_getFinalizedHead";
	// 	const RESPONSE: &[u8] = b"unexpected response";

	// 	let request_body = json!({
	// 		"jsonrpc": "2.0",
	// 		"id": 1,
	// 		"method": RPC_METHOD,
	// 		"params": Vec::<&str>::new()
	// 	});

	// 	let request_body_slice: &[u8] = &(serde_json::to_vec(&request_body).unwrap())[..];

	// 	{
	// 		let mut state = state.write();

	// 		state.expect_request(testing::PendingRequest {
	// 			method: "POST".into(),
	// 			uri: RPC_REQUEST_URL.into(),
	// 			body: request_body_slice.to_vec(),
	// 			headers: vec![(
	// 				"Content-Type".to_string(),
	// 				"application/json;charset=utf-8".to_string()
	// 			)],
	// 			response: Some(RESPONSE.to_vec()),
	// 			sent: true,
	// 			..Default::default()
	// 		});
	// 	}

	// 	t.execute_with(|| {
	// 		let request = Request {
	// 			method: RPC_METHOD,
	// 			..Default::default()
	// 		};

	// 		let response = request.send().unwrap_err();

	// 		assert_eq!(Error::Deserializing, response);
	// 	})
	// }
}
