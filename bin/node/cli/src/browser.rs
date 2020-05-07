// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

use crate::chain_spec::ChainSpec;
use log::info;
use wasm_bindgen::prelude::*;
use browser_utils::{
	Client,
	browser_configuration, set_console_error_panic_hook, init_console_log,
};
use std::str::FromStr;

/// Starts the client.
#[wasm_bindgen]
pub async fn start_client(chain_spec: Option<String>, log_level: String) -> Result<Client, JsValue> {
	start_inner(chain_spec, log_level)
		.await
		.map_err(|err| JsValue::from_str(&err.to_string()))
}

async fn start_inner(chain_spec: Option<String>, log_level: String) -> Result<Client, Box<dyn std::error::Error>> {
	set_console_error_panic_hook();
	init_console_log(log::Level::from_str(&log_level)?)?;
	let chain_spec = match chain_spec {
		Some(chain_spec) => ChainSpec::from_json_bytes(chain_spec.as_bytes().to_vec())
			.map_err(|e| format!("{:?}", e))?,
		None => crate::chain_spec::development_config(),
	};

	let config = browser_configuration(chain_spec).await?;

	info!("Substrate browser node");
	info!("✌️  version {}", config.impl_version);
	info!("❤️  by Parity Technologies, 2017-2020");
	info!("📋 Chain specification: {}", config.chain_spec.name());
	info!("🏷  Node name: {}", config.network.node_name);
	info!("👤 Role: {:?}", config.role);

	// Create the service. This is the most heavy initialization step.
	let service = crate::service::new_light(config)
		.map_err(|e| format!("{:?}", e))?;

	Ok(browser_utils::start_client(service))
}
