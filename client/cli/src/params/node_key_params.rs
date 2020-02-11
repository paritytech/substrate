// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

use std::{path::PathBuf, str::FromStr};
use structopt::StructOpt;
use sc_service::{Configuration, RuntimeGenesis};
use sc_network::config::NodeKeyConfig;
use sp_core::H256;

use crate::error;
use crate::arg_enums::NodeKeyType;

/// The file name of the node's Ed25519 secret key inside the chain-specific
/// network config directory, if neither `--node-key` nor `--node-key-file`
/// is specified in combination with `--node-key-type=ed25519`.
const NODE_KEY_ED25519_FILE: &str = "secret_ed25519";

/// Parameters used to create the `NodeKeyConfig`, which determines the keypair
/// used for libp2p networking.
#[derive(Debug, StructOpt, Clone)]
pub struct NodeKeyParams {
	/// The secret key to use for libp2p networking.
	///
	/// The value is a string that is parsed according to the choice of
	/// `--node-key-type` as follows:
	///
	///   `ed25519`:
	///   The value is parsed as a hex-encoded Ed25519 32 bytes secret key,
	///   i.e. 64 hex characters.
	///
	/// The value of this option takes precedence over `--node-key-file`.
	///
	/// WARNING: Secrets provided as command-line arguments are easily exposed.
	/// Use of this option should be limited to development and testing. To use
	/// an externally managed secret key, use `--node-key-file` instead.
	#[structopt(long = "node-key", value_name = "KEY")]
	pub node_key: Option<String>,

	/// The type of secret key to use for libp2p networking.
	///
	/// The secret key of the node is obtained as follows:
	///
	///   * If the `--node-key` option is given, the value is parsed as a secret key
	///     according to the type. See the documentation for `--node-key`.
	///
	///   * If the `--node-key-file` option is given, the secret key is read from the
	///     specified file. See the documentation for `--node-key-file`.
	///
	///   * Otherwise, the secret key is read from a file with a predetermined,
	///     type-specific name from the chain-specific network config directory
	///     inside the base directory specified by `--base-dir`. If this file does
	///     not exist, it is created with a newly generated secret key of the
	///     chosen type.
	///
	/// The node's secret key determines the corresponding public key and hence the
	/// node's peer ID in the context of libp2p.
	#[structopt(
		long = "node-key-type",
		value_name = "TYPE",
		possible_values = &NodeKeyType::variants(),
		case_insensitive = true,
		default_value = "Ed25519"
	)]
	pub node_key_type: NodeKeyType,

	/// The file from which to read the node's secret key to use for libp2p networking.
	///
	/// The contents of the file are parsed according to the choice of `--node-key-type`
	/// as follows:
	///
	///   `ed25519`:
	///   The file must contain an unencoded 32 bytes Ed25519 secret key.
	///
	/// If the file does not exist, it is created with a newly generated secret key of
	/// the chosen type.
	#[structopt(long = "node-key-file", value_name = "FILE")]
	pub node_key_file: Option<PathBuf>,
}

impl NodeKeyParams {
	/// Create a `NodeKeyConfig` from the given `NodeKeyParams` in the context
	/// of an optional network config storage directory.
	pub fn update_config<'a, G, E>(
		&self,
		mut config: &'a mut Configuration<G, E>,
		net_config_path: Option<&PathBuf>,
	) -> error::Result<&'a NodeKeyConfig>
	where
		G: RuntimeGenesis,
	{
		config.network.node_key = match self.node_key_type {
			NodeKeyType::Ed25519 => {
				let secret = if let Some(node_key) = self.node_key.as_ref() {
					parse_ed25519_secret(node_key)?
				} else {
					let path = self.node_key_file.clone()
						.or_else(|| net_config_path.map(|d| d.join(NODE_KEY_ED25519_FILE)));

					if let Some(path) = path {
						sc_network::config::Secret::File(path)
					} else {
						sc_network::config::Secret::New
					}
				};

				NodeKeyConfig::Ed25519(secret)
			}
		};

		Ok(&config.network.node_key)
	}
}

/// Create an error caused by an invalid node key argument.
fn invalid_node_key(e: impl std::fmt::Display) -> error::Error {
	error::Error::Input(format!("Invalid node key: {}", e))
}

/// Parse a Ed25519 secret key from a hex string into a `sc_network::Secret`.
fn parse_ed25519_secret(hex: &str) -> error::Result<sc_network::config::Ed25519Secret> {
	H256::from_str(&hex).map_err(invalid_node_key).and_then(|bytes|
		sc_network::config::identity::ed25519::SecretKey::from_bytes(bytes)
			.map(sc_network::config::Secret::Input)
			.map_err(invalid_node_key))
}

#[cfg(test)]
mod tests {
	use sc_network::config::identity::ed25519;
	use super::*;

	#[test]
	fn test_node_key_config_input() {
		fn secret_input(net_config_dir: Option<&PathBuf>) -> error::Result<()> {
			NodeKeyType::variants().iter().try_for_each(|t| {
				let mut config = Configuration::<(), ()>::default();
				let node_key_type = NodeKeyType::from_str(t).unwrap();
				let sk = match node_key_type {
					NodeKeyType::Ed25519 => ed25519::SecretKey::generate().as_ref().to_vec()
				};
				let params = NodeKeyParams {
					node_key_type,
					node_key: Some(format!("{:x}", H256::from_slice(sk.as_ref()))),
					node_key_file: None
				};
				params.update_config(&mut config, net_config_dir).and_then(|c| match c {
					NodeKeyConfig::Ed25519(sc_network::config::Secret::Input(ref ski))
						if node_key_type == NodeKeyType::Ed25519 &&
							&sk[..] == ski.as_ref() => Ok(()),
					_ => Err(error::Error::Input("Unexpected node key config".into()))
				})
			})
		}

		assert!(secret_input(None).is_ok());
		assert!(secret_input(Some(&PathBuf::from_str("x").unwrap())).is_ok());
	}

	#[test]
	fn test_node_key_config_file() {
		fn secret_file(net_config_dir: Option<&PathBuf>) -> error::Result<()> {
			NodeKeyType::variants().iter().try_for_each(|t| {
				let mut config = Configuration::<(), ()>::default();
				let node_key_type = NodeKeyType::from_str(t).unwrap();
				let tmp = tempfile::Builder::new().prefix("alice").tempdir()?;
				let file = tmp.path().join(format!("{}_mysecret", t)).to_path_buf();
				let params = NodeKeyParams {
					node_key_type,
					node_key: None,
					node_key_file: Some(file.clone())
				};
				params.update_config(&mut config, net_config_dir).and_then(|c| match c {
					NodeKeyConfig::Ed25519(sc_network::config::Secret::File(ref f))
						if node_key_type == NodeKeyType::Ed25519 && f == &file => Ok(()),
					_ => Err(error::Error::Input("Unexpected node key config".into()))
				})
			})
		}

		assert!(secret_file(None).is_ok());
		assert!(secret_file(Some(&PathBuf::from_str("x").unwrap())).is_ok());
	}

	#[test]
	fn test_node_key_config_default() {
		fn with_def_params<F>(f: F) -> error::Result<()>
		where
			F: Fn(NodeKeyParams) -> error::Result<()>
		{
			NodeKeyType::variants().iter().try_for_each(|t| {
				let node_key_type = NodeKeyType::from_str(t).unwrap();
				f(NodeKeyParams {
					node_key_type,
					node_key: None,
					node_key_file: None
				})
			})
		}

		fn no_config_dir() -> error::Result<()> {
			with_def_params(|params| {
				let mut config = Configuration::<(), ()>::default();
				let typ = params.node_key_type;
				params.update_config(&mut config, None)
					.and_then(|c| match c {
						NodeKeyConfig::Ed25519(sc_network::config::Secret::New)
							if typ == NodeKeyType::Ed25519 => Ok(()),
						_ => Err(error::Error::Input("Unexpected node key config".into()))
					})
			})
		}

		fn some_config_dir(net_config_dir: &PathBuf) -> error::Result<()> {
			with_def_params(|params| {
				let mut config = Configuration::<(), ()>::default();
				let dir = PathBuf::from(net_config_dir.clone());
				let typ = params.node_key_type;
				params.update_config(&mut config, Some(net_config_dir))
					.and_then(move |c| match c {
						NodeKeyConfig::Ed25519(sc_network::config::Secret::File(ref f))
							if typ == NodeKeyType::Ed25519 &&
								f == &dir.join(NODE_KEY_ED25519_FILE) => Ok(()),
						_ => Err(error::Error::Input("Unexpected node key config".into()))
				})
			})
		}

		assert!(no_config_dir().is_ok());
		assert!(some_config_dir(&PathBuf::from_str("x").unwrap()).is_ok());
	}
}
