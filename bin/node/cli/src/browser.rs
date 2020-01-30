// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

use crate::ChainSpec;
use log::info;
use wasm_bindgen::prelude::*;
use sc_service::Configuration;
use browser_utils::{
	Transport, Client,
	browser_configuration, set_console_error_panic_hook, init_console_log,
};

/// Starts the client.
#[wasm_bindgen]
pub async fn start_client(wasm_ext: Transport) -> Result<Client, JsValue> {
	start_inner(wasm_ext)
		.await
		.map_err(|err| JsValue::from_str(&err.to_string()))
}

async fn start_inner(wasm_ext: Transport) -> Result<Client, Box<dyn std::error::Error>> {
	set_console_error_panic_hook();
	init_console_log(log::Level::Info)?;

	let chain_spec = ChainSpec::FlamingFir.load()
		.map_err(|e| format!("{:?}", e))?;

	let config: Configuration<_, _> = browser_configuration(wasm_ext, chain_spec)
		.await?;

	info!("Substrate browser node");
	info!("  version {}", config.full_version());
	info!("  by Parity Technologies, 2017-2020");
	info!("Chain specification: {}", config.expect_chain_spec().name());
	info!("Node name: {}", config.name);
	info!("Roles: {:?}", config.roles);

	// Create the service. This is the most heavy initialization step.
	let service = crate::service::new_light(config)
		.map_err(|e| format!("{:?}", e))?;

	Ok(browser_utils::start_client(service))
}
