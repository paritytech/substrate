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
//! `sp-io` crate exposes a low level methods to make and control RPC requests
//! available only for Offchain Workers. Those might be hard to use
//! and usually that level of control is not really necessary.

// use frame_support::{debug};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use crate::{RuntimeDebug, offchain::Duration};
use serde_json::json;
use sp_std::{vec::Vec, str};
// use sp_core::RuntimeDebug;
// use crate::offchain::Duration;
use super::http;

// /// A rpc call error
// #[derive(Clone, PartialEq, Eq, RuntimeDebug)]
// pub enum Error {
// 	ParsingError,
// 	/// Request had timed out.
// 	CallError(),
// }

// pub type RpcResult = Result<Response, Error>;

#[derive(Deserialize, Default, RuntimeDebug)]
pub struct Response {
	#[serde(deserialize_with = "de_string_to_bytes")]
	pub jsonrpc: Vec<u8>,
	#[serde(deserialize_with = "de_string_to_bytes")]
	pub result: Vec<u8>,
	pub id: u32
}

pub struct Request<'a> {
	pub jsonrpc: &'a str,
	pub id: u32,
	pub method: &'a str,
	pub params: Vec<&'a str>,
	pub timeout: u64,
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
	pub fn send(&self) -> Result<Response, http::Error> {
		let request_body = json!({
			"jsonrpc": self.jsonrpc,
			"id": self.id,
			"method": self.method,
			"params": self.params
		});

		// debug::info!("========================= BODY CONSTRUCT ==================== {:?}", serde_json::to_string(&request_body).unwrap());

		let mut body: Vec<&[u8]> = Vec::new();
		// let request_body_vec: Vec<u8> = serde_json::to_vec(&request_body).unwrap();
		let request_body_slice: &[u8] = &(serde_json::to_vec(&request_body).unwrap())[..];
		// let request_body_slice: &[u8] = &v[..];
		body.push(request_body_slice);

		let post_request = http::Request::post(self.url, body);

		let timeout = sp_io::offchain::timestamp().add(Duration::from_millis(self.timeout));

		let pending = post_request
			.add_header("Content-Type", "application/json;charset=utf-8")
			.deadline(timeout)
			.send().map_err(|_| http::Error::IoError)?;

		let response = pending.try_wait(timeout)
			.map_err(|_| http::Error::DeadlineReached)??;

		if response.code != 200 {
			log::warn!("Unexpected status code: {}", response.code);
			return Err(http::Error::Unknown);
		}

		let response_body_bytes = response.body().collect::<Vec<u8>>();

		let response_body_str = str::from_utf8(&response_body_bytes).map_err(|_| http::Error::Unknown)?;

		log::info!("=================== RESPONSE RAW ================== {:?}", response_body_str);


		let rpc_response: Response = serde_json::from_str(&response_body_str).map_err(|_| http::Error::Unknown)?;

		Ok(rpc_response)
	}
}
