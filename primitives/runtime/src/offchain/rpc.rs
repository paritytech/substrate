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
// ! use sp_runtime::offchain::rpc::Request;
// !
// ! let client = Client::new();
// ! let request = Request::new();
// ! let rpc_result = client.send(&request);
// !
// ! match rpc_result {
// ! 	Ok(response) => {
// ! 		if response.result.is_some() {
// ! 			log::info!("Rpc call result: {:?}", response.result);
// ! 		} else {
// ! 			let error = response.error.unwrap();
// ! 			log::error!(
// ! 				"Rpc call error: code: {:?}, message: {:?}, data: {:?}",
// ! 				error.code,
// ! 				error.message,
// !                error.data
// ! 			);
// ! 		}
// ! 	},
// ! 	Err(e) => {
// ! 		log::error!("Rpc call error: {:?}", e);
// ! 	}
// ! }

use crate::{RuntimeDebug, offchain::Duration, offchain::Timestamp};
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
#[derive(Clone, RuntimeDebug)]
pub struct Request<'a> {
	/// rpc request jsonrpc
	pub jsonrpc: &'a str,
	/// rpc request id
	pub id: u32,
	/// rpc request method
	pub method: &'a str,
	/// rpc request params
	pub params: Vec<&'a str>,
}

/// A rpc client
#[derive(Clone, RuntimeDebug)]
pub struct Client<'a> {
	/// RPC request timeout in milliseconds.
	pub timeout: u64,
	/// HTTP URL to send the RPC request to.
	pub url: &'a str,
}

impl<'a> Default for Request<'a> {
	fn default() -> Self {
		Request {
			jsonrpc: "2.0",
			id: 1,
			method: "chain_getFinalizedHead",
			params: Vec::new(),
		}
	}
}

impl<'a> Default for Client<'a> {
	fn default() -> Self {
		Client {
			timeout: 3_000,
			url: "http://localhost:9933"
		}
	}
}

impl<'a> Request<'a> {
	/// Create a new Request
	pub fn new() -> Self {
		Request::default()
	}

	/// Change the Method for the Request
	pub fn method(mut self, method: &'a str) -> Self {
		self.method = method;
		self
	}

	/// Change the Params for the Request
	pub fn params(mut self, params: Vec<&'a str>) -> Self {
		self.params = params;
		self
	}

	/// Change the Jsonrpc for the Request
	pub fn jsonrpc(mut self, jsonrpc: &'a str) -> Self {
		self.jsonrpc = jsonrpc;
		self
	}

	/// Change the ID for the Request
	pub fn id(mut self, id: u32) -> Self {
		self.id = id;
		self
	}
}

impl<'a> Client<'a> {
	/// Create a new Client
	pub fn new() -> Self {
		Client::default()
	}

  /// Change the URL for the Client
	pub fn url(mut self, url: &'a str) -> Self {
		self.url = url;
		self
	}

  /// Change the Timeout for the Client
	pub fn timeout(mut self, timeout: u64) -> Self {
		self.timeout = timeout;
		self
	}

  /// Send the request and return a RPC result.
	///
	/// Err is returned in case there is a Http
	/// or deserializing error.
	pub fn send(&self, request: &'a Request) -> RpcResult {
		let deadline = sp_io::offchain::timestamp().add(Duration::from_millis(self.timeout));
		self.send_with_deadline(deadline, request)
	}

	/// Send the request and return a RPC result.
	/// Deadline is used instead of Timeout
	/// Err is returned in case there is a Http
	/// or deserializing error.
	pub fn send_with_deadline(&self, deadline: Timestamp, request: &'a Request) -> RpcResult {
		// Construct http POST body
		let request_body = json!({
			"jsonrpc": request.jsonrpc,
			"id": request.id,
			"method": request.method,
			"params": request.params
		});
		let mut body: Vec<&[u8]> = Vec::new();
		let request_body_slice: &[u8] = &(serde_json::to_vec(&request_body).unwrap())[..];
		body.push(request_body_slice);

		// Send http POST request
		let post_request = http::Request::post(self.url, body);

		let pending = match post_request
			.add_header("Content-Type", "application/json;charset=utf-8")
			.deadline(deadline)
			.send().map_err(|_| http::Error::IoError) {
				Ok(result) => result,
				Err(e) => return Err(Error::Http(e)),
		};

		// Hanlde http response
		let response = match pending.try_wait(deadline)
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

	/// Deserialize a RPC response
	pub fn deserialize_response(response_body_bytes: &Vec<u8>) -> RpcResult {
		let response_deserialized: Value = serde_json::from_slice(response_body_bytes)
			.map_err(|_| Error::Deserializing)?;

		response_deserialized.as_object().ok_or(Error::Deserializing)?;

		let jsonrpc_value = response_deserialized.get("jsonrpc").ok_or(Error::Deserializing)?;
		let jsonrpc = jsonrpc_value.as_str().ok_or(Error::Deserializing)?;

		let id_value = response_deserialized.get("id").ok_or(Error::Deserializing)?;
		let id = id_value.as_u64().ok_or(Error::Deserializing)?;

		let result_value = response_deserialized.get("result");
		let error_value = response_deserialized.get("error");

		if error_value == None && result_value == None {
			return Err(Error::Deserializing);
		}

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
	use sp_core::{offchain::{OffchainWorkerExt, testing}};

	const RPC_REQUEST_URL: &'static str = "http://localhost:9933";

	/// Helper function to assess expected response
	fn assess_response(
		body: &Value,
    client: &Client,
		request: &Request,
		response: &[u8],
		expected_result: &RpcResult
	) {
		let (offchain, state) = testing::TestOffchainExt::new();
		let mut t = TestExternalities::default();
		t.register_extension(OffchainWorkerExt::new(offchain));

		let request_body_slice: &[u8] = &(serde_json::to_vec(body).unwrap())[..];

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
				response: Some(response.to_vec()),
				sent: true,
				..Default::default()
			});
		}

		t.execute_with(|| {
			let rpc_result = (*client).send(request);
			assert_eq!(*expected_result, rpc_result);
		})
	}

	#[test]
	fn should_return_rpc_result() {
		const RESPONSE: &[u8] =
			br#"{"jsonrpc":"2.0","result":"0x3141..98123b","id":1}"#;
		const EXPECTED_RESULT: &[u8] = b"0x3141..98123b";
		const RPC_METHOD: &'static str = "chain_getFinalizedHead";

		let body = json!({
			"jsonrpc": "2.0",
			"id": 1,
			"method": RPC_METHOD,
			"params": Vec::<&str>::new()
		});

		let expected_response = Response {
			jsonrpc: b"2.0".to_vec(),
			result: Some(json!(str::from_utf8(EXPECTED_RESULT).unwrap())),
			error: None,
			id: 1,
		};

		let expected_result = Ok(expected_response);

    let client = Client::new();
		let request = Request::new();

		assess_response(&body, &client, &request, &RESPONSE, &expected_result);
	}

	#[test]
	fn should_return_rpc_error() {
		const RPC_METHOD: &'static str = "chain_madeUpMethod";
		const RESPONSE: &[u8] =
			br#"{"jsonrpc":"2.0","error":{"code":-32601,"message":"Method not found"},"id":1}"#;
		const EXPECTED_ERROR_CODE: i32 = -32601;
		const EXPECTED_ERROR_MESSAGE: &[u8] = b"Method not found";

		let body = json!({
			"jsonrpc": "2.0",
			"id": 1,
			"method": RPC_METHOD,
			"params": Vec::<&str>::new()
		});

		let expected_rpc_error = RpcError {
			code: EXPECTED_ERROR_CODE,
			message: EXPECTED_ERROR_MESSAGE.to_vec(),
			data: None
		};

		let expected_response = Response {
			jsonrpc: b"2.0".to_vec(),
			result: None,
			error: Some(expected_rpc_error),
			id: 1,
		};

		let expected_result = Ok(expected_response);

    let client = Client::new();
		let request = Request::new().method(RPC_METHOD);

		assess_response(&body, &client, &request, RESPONSE, &expected_result);
	}

	#[test]
	fn should_return_deserializing_error() {
		const RPC_METHOD: &'static str = "chain_getFinalizedHead";
		const RESPONSES: [&[u8]; 10] = [
			b"unexpected response", // Not an object
			br#"{"jsonrpc":2,"result":"0x3141..98123b","id":1}"#, // Invalid jsonrpc
			br#"{"jsonrpc":"2.0","result":"0x3141..98123b","id":"1"}"#, // Invalid id
			br#"{"result":"0x3141..98123b","id":"1"}"#, // jsonrpc not present
			br#"{"jsonrpc":"2.0","result":"0x3141..98123b"}"#, // id not present
			br#"{"jsonrpc":"2.0","id":1}"#, // Neither result nor error present
			br#"{"jsonrpc":"2.0","error":{"code":"-32601","message":"Method not found"},"id":1}"#, // Invalid code
			br#"{"jsonrpc":"2.0","error":{"code":-32601,"message":1},"id":1}"#, // Invalid message
			br#"{"jsonrpc":"2.0","error":{"message":"message"},"id":1}"#, // code not present
			br#"{"jsonrpc":"2.0","error":{"code":-32601},"id":1}"#, // message not present
		];

		let body = json!({
			"jsonrpc": "2.0",
			"id": 1,
			"method": RPC_METHOD,
			"params": Vec::<&str>::new()
		});

		let expected_response = Error::Deserializing;
		let expected_result = Err(expected_response);

    let client = Client::new();
		let request = Request::new();

		for response in RESPONSES.iter() {
			assess_response(&body, &client, &request, response, &expected_result);
		}
	}
}
