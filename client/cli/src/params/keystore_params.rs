// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use crate::{error, error::Result};
use clap::Args;
use sc_service::config::KeystoreConfig;
use sp_core::crypto::SecretString;
use std::{
	fs,
	path::{Path, PathBuf},
};

/// default sub directory for the key store
const DEFAULT_KEYSTORE_CONFIG_PATH: &str = "keystore";

/// Parameters of the keystore
#[derive(Debug, Clone, Args)]
pub struct KeystoreParams {
	/// Specify custom URIs to connect to for keystore-services
	#[arg(long)]
	pub keystore_uri: Option<String>,

	/// Specify custom keystore path.
	#[arg(long, value_name = "PATH")]
	pub keystore_path: Option<PathBuf>,

	/// Use interactive shell for entering the password used by the keystore.
	#[arg(long, conflicts_with_all = &["password", "password_filename"])]
	pub password_interactive: bool,

	/// Password used by the keystore. This allows appending an extra user-defined secret to the
	/// seed.
	#[arg(
		long,
		value_parser = secret_string_from_str,
		conflicts_with_all = &["password_interactive", "password_filename"]
	)]
	pub password: Option<SecretString>,

	/// File that contains the password used by the keystore.
	#[arg(
		long,
		value_name = "PATH",
		conflicts_with_all = &["password_interactive", "password"]
	)]
	pub password_filename: Option<PathBuf>,
}

/// Parse a sercret string, returning a displayable error.
pub fn secret_string_from_str(s: &str) -> std::result::Result<SecretString, String> {
	std::str::FromStr::from_str(s).map_err(|_| "Could not get SecretString".to_string())
}

impl KeystoreParams {
	/// Get the keystore configuration for the parameters
	pub fn keystore_config(&self, config_dir: &Path) -> Result<KeystoreConfig> {
		let password = if self.password_interactive {
			Some(SecretString::new(input_keystore_password()?))
		} else if let Some(ref file) = self.password_filename {
			let password = fs::read_to_string(file).map_err(|e| format!("{}", e))?;
			Some(SecretString::new(password))
		} else {
			self.password.clone()
		};

		let path = self
			.keystore_path
			.clone()
			.unwrap_or_else(|| config_dir.join(DEFAULT_KEYSTORE_CONFIG_PATH));

		Ok(KeystoreConfig::Path { path, password })
	}

	/// helper method to fetch password from `KeyParams` or read from stdin
	pub fn read_password(&self) -> error::Result<Option<SecretString>> {
		let (password_interactive, password) = (self.password_interactive, self.password.clone());

		let pass = if password_interactive {
			let password = rpassword::prompt_password("Key password: ")?;
			Some(SecretString::new(password))
		} else {
			password
		};

		Ok(pass)
	}
}

fn input_keystore_password() -> Result<String> {
	rpassword::prompt_password("Keystore password: ").map_err(|e| format!("{:?}", e).into())
}
