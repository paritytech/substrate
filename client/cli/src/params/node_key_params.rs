// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

use clap::Args;
use sc_network::config::{identity::ed25519, NodeKeyConfig};
use sp_core::H256;
use std::{path::PathBuf, str::FromStr};

use crate::{arg_enums::NodeKeyType, error};

/// The file name of the node's Ed25519 secret key inside the chain-specific
/// network config directory, if neither `--node-key` nor `--node-key-file`
/// is specified in combination with `--node-key-type=ed25519`.
const NODE_KEY_ED25519_FILE: &str = "secret_ed25519";

/// Parameters used to create the `NodeKeyConfig`, which determines the keypair
/// used for libp2p networking.
#[derive(Debug, Clone, Args)]
pub struct NodeKeyParams {
	/// The secret key to use for libp2p networking.
	///
	/// The value is a string that is parsed according to the choice of
	/// `--node-key-type` as follows:
	///
	///   `ed25519`:
	///   The value is parsed as a hex-encoded Ed25519 32 byte secret key,
	///   i.e. 64 hex characters.
	///
	/// The value of this option takes precedence over `--node-key-file`.
	///
	/// WARNING: Secrets provided as command-line arguments are easily exposed.
	/// Use of this option should be limited to development and testing. To use
	/// an externally managed secret key, use `--node-key-file` instead.
	#[clap(long, value_name = "KEY")]
	pub node_key: Option<String>,

	/// The type of secret key to use for libp2p networking.
	///
	/// The secret key of the node is obtained as follows:
	///
	///   * If the `--node-key` option is given, the value is parsed as a secret key according to
	///     the type. See the documentation for `--node-key`.
	///
	///   * If the `--node-key-file` option is given, the secret key is read from the specified
	///     file. See the documentation for `--node-key-file`.
	///
	///   * Otherwise, the secret key is read from a file with a predetermined, type-specific name
	///     from the chain-specific network config directory inside the base directory specified by
	///     `--base-dir`. If this file does not exist, it is created with a newly generated secret
	///     key of the chosen type.
	///
	/// The node's secret key determines the corresponding public key and hence the
	/// node's peer ID in the context of libp2p.
	#[clap(long, value_name = "TYPE", arg_enum, ignore_case = true, default_value = "ed25519")]
	pub node_key_type: NodeKeyType,

	/// The file from which to read the node's secret key to use for libp2p networking.
	///
	/// The contents of the file are parsed according to the choice of `--node-key-type`
	/// as follows:
	///
	///   `ed25519`:
	///   The file must contain an unencoded 32 byte or hex encoded Ed25519 secret key.
	///
	/// If the file does not exist, it is created with a newly generated secret key of
	/// the chosen type.
	#[clap(long, value_name = "FILE")]
	pub node_key_file: Option<PathBuf>,
}

impl NodeKeyParams {
	/// Create a `NodeKeyConfig` from the given `NodeKeyParams` in the context
	/// of an optional network config storage directory.
	pub fn node_key(&self, net_config_dir: &PathBuf) -> error::Result<NodeKeyConfig> {
		Ok(match self.node_key_type {
			NodeKeyType::Ed25519 => {
				let secret = if let Some(node_key) = self.node_key.as_ref() {
					parse_ed25519_secret(node_key)?
				} else {
					sc_network::config::Secret::File(
						self.node_key_file
							.clone()
							.unwrap_or_else(|| net_config_dir.join(NODE_KEY_ED25519_FILE)),
					)
				};

				NodeKeyConfig::Ed25519(secret)
			},
		})
	}
}

/// Create an error caused by an invalid node key argument.
fn invalid_node_key(e: impl std::fmt::Display) -> error::Error {
	error::Error::Input(format!("Invalid node key: {}", e))
}

/// Parse a Ed25519 secret key from a hex string into a `sc_network::Secret`.
fn parse_ed25519_secret(hex: &str) -> error::Result<sc_network::config::Ed25519Secret> {
	H256::from_str(&hex).map_err(invalid_node_key).and_then(|bytes| {
		ed25519::SecretKey::from_bytes(bytes)
			.map(sc_network::config::Secret::Input)
			.map_err(invalid_node_key)
	})
}

#[cfg(test)]
mod tests {
	use super::*;
	use clap::ArgEnum;
	use sc_network::config::identity::{ed25519, Keypair};
	use std::fs;

	#[test]
	fn test_node_key_config_input() {
		fn secret_input(net_config_dir: &PathBuf) -> error::Result<()> {
			NodeKeyType::value_variants().iter().try_for_each(|t| {
				let node_key_type = *t;
				let sk = match node_key_type {
					NodeKeyType::Ed25519 => ed25519::SecretKey::generate().as_ref().to_vec(),
				};
				let params = NodeKeyParams {
					node_key_type,
					node_key: Some(format!("{:x}", H256::from_slice(sk.as_ref()))),
					node_key_file: None,
				};
				params.node_key(net_config_dir).and_then(|c| match c {
					NodeKeyConfig::Ed25519(sc_network::config::Secret::Input(ref ski))
						if node_key_type == NodeKeyType::Ed25519 && &sk[..] == ski.as_ref() =>
						Ok(()),
					_ => Err(error::Error::Input("Unexpected node key config".into())),
				})
			})
		}

		assert!(secret_input(&PathBuf::from_str("x").unwrap()).is_ok());
	}

	#[test]
	fn test_node_key_config_file() {
		fn check_key(file: PathBuf, key: &ed25519::SecretKey) {
			let params = NodeKeyParams {
				node_key_type: NodeKeyType::Ed25519,
				node_key: None,
				node_key_file: Some(file),
			};

			let node_key = params
				.node_key(&PathBuf::from("not-used"))
				.expect("Creates node key config")
				.into_keypair()
				.expect("Creates node key pair");

			match node_key {
				Keypair::Ed25519(ref pair) if pair.secret().as_ref() == key.as_ref() => {},
				_ => panic!("Invalid key"),
			}
		}

		let tmp = tempfile::Builder::new().prefix("alice").tempdir().expect("Creates tempfile");
		let file = tmp.path().join("mysecret").to_path_buf();
		let key = ed25519::SecretKey::generate();

		fs::write(&file, hex::encode(key.as_ref())).expect("Writes secret key");
		check_key(file.clone(), &key);

		fs::write(&file, &key).expect("Writes secret key");
		check_key(file.clone(), &key);
	}

	#[test]
	fn test_node_key_config_default() {
		fn with_def_params<F>(f: F) -> error::Result<()>
		where
			F: Fn(NodeKeyParams) -> error::Result<()>,
		{
			NodeKeyType::value_variants().iter().try_for_each(|t| {
				let node_key_type = *t;
				f(NodeKeyParams { node_key_type, node_key: None, node_key_file: None })
			})
		}

		fn some_config_dir(net_config_dir: &PathBuf) -> error::Result<()> {
			with_def_params(|params| {
				let dir = PathBuf::from(net_config_dir.clone());
				let typ = params.node_key_type;
				params.node_key(net_config_dir).and_then(move |c| match c {
					NodeKeyConfig::Ed25519(sc_network::config::Secret::File(ref f))
						if typ == NodeKeyType::Ed25519 && f == &dir.join(NODE_KEY_ED25519_FILE) =>
						Ok(()),
					_ => Err(error::Error::Input("Unexpected node key config".into())),
				})
			})
		}

		assert!(some_config_dir(&PathBuf::from_str("x").unwrap()).is_ok());
	}
}
