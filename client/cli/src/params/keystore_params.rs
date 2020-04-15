// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

use crate::error::Result;
use sc_service::config::KeystoreConfig;
use std::fs;
use std::path::PathBuf;
use structopt::StructOpt;

/// default sub directory for the key store
const DEFAULT_KEYSTORE_CONFIG_PATH: &'static str = "keystore";

/// Parameters of the keystore
#[derive(Debug, StructOpt, Clone)]
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
		conflicts_with_all = &[ "password-interactive", "password-filename" ]
	)]
	pub password: Option<String>,

	/// File that contains the password used by the keystore.
	#[structopt(
		long = "password-filename",
		value_name = "PATH",
		parse(from_os_str),
		conflicts_with_all = &[ "password-interactive", "password" ]
	)]
	pub password_filename: Option<PathBuf>,
}

impl KeystoreParams {
	/// Get the keystore configuration for the parameters
	pub fn keystore_config(&self, base_path: &PathBuf) -> Result<KeystoreConfig> {
		let password = if self.password_interactive {
			#[cfg(not(target_os = "unknown"))]
			{
				Some(input_keystore_password()?.into())
			}
			#[cfg(target_os = "unknown")]
			None
		} else if let Some(ref file) = self.password_filename {
			Some(
				fs::read_to_string(file)
					.map_err(|e| format!("{}", e))?
					.into(),
			)
		} else if let Some(ref password) = self.password {
			Some(password.clone().into())
		} else {
			None
		};

		let path = self
			.keystore_path
			.clone()
			.unwrap_or(base_path.join(DEFAULT_KEYSTORE_CONFIG_PATH));

		Ok(KeystoreConfig::Path { path, password })
	}
}

#[cfg(not(target_os = "unknown"))]
fn input_keystore_password() -> Result<String> {
	rpassword::read_password_from_tty(Some("Keystore password: "))
		.map_err(|e| format!("{:?}", e).into())
}
