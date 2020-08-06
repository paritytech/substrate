// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use crate::error::Result;
use sc_service::config::KeystoreConfig;
use std::fs;
use std::path::PathBuf;
use structopt::StructOpt;
use sp_core::crypto::SecretString;

/// default sub directory for the key store
const DEFAULT_KEYSTORE_CONFIG_PATH: &'static str = "keystore";

/// Parameters of the keystore
#[derive(Debug, StructOpt)]
pub struct KeystoreParams {
	/// Specify custom keystore path.
	#[structopt(long = "keystore-path", value_name = "PATH", parse(from_os_str))]
	pub keystore_path: Option<PathBuf>,

	/// Use interactive shell for entering the password used by the keystore.
	#[structopt(
		long = "password-interactive",
		conflicts_with_all = &[ "password", "password-filename" ]
	)]
	pub password_interactive: bool,

	/// Password used by the keystore.
	#[structopt(
		long = "password",
		parse(try_from_str = secret_string_from_str),
		conflicts_with_all = &[ "password-interactive", "password-filename" ]
	)]
	pub password: Option<SecretString>,

	/// File that contains the password used by the keystore.
	#[structopt(
		long = "password-filename",
		value_name = "PATH",
		parse(from_os_str),
		conflicts_with_all = &[ "password-interactive", "password" ]
	)]
	pub password_filename: Option<PathBuf>,
}

/// Parse a sercret string, returning a displayable error.
pub fn secret_string_from_str(s: &str) -> std::result::Result<SecretString, String> {
	Ok(std::str::FromStr::from_str(s)
		.map_err(|_e| "Could not get SecretString".to_string())?)
}

impl KeystoreParams {
	/// Get the keystore configuration for the parameters
	pub fn keystore_config(&self, base_path: &PathBuf) -> Result<KeystoreConfig> {
		let password = if self.password_interactive {
			#[cfg(not(target_os = "unknown"))]
			{
				let mut password = input_keystore_password()?;
				let secret = std::str::FromStr::from_str(password.as_str())
					.map_err(|()| "Error reading password")?;
				use sp_core::crypto::Zeroize;
				password.zeroize();
				Some(secret)
			}
			#[cfg(target_os = "unknown")]
			None
		} else if let Some(ref file) = self.password_filename {
			let mut password = fs::read_to_string(file)
				.map_err(|e| format!("{}", e))?;
			let secret = std::str::FromStr::from_str(password.as_str())
				.map_err(|()| "Error reading password")?;
			use sp_core::crypto::Zeroize;
			password.zeroize();
			Some(secret)
		} else {
			self.password.clone()
		};

		let path = self
			.keystore_path
			.clone()
			.unwrap_or_else(|| base_path.join(DEFAULT_KEYSTORE_CONFIG_PATH));

		Ok(KeystoreConfig::Path { path, password })
	}
}

#[cfg(not(target_os = "unknown"))]
fn input_keystore_password() -> Result<String> {
	rpassword::read_password_from_tty(Some("Keystore password: "))
		.map_err(|e| format!("{:?}", e).into())
}
