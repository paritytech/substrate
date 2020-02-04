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

use sc_network::{
	self,
	config::{
		NodeKeyConfig,
	},
};
use sp_core::H256;
use regex::Regex;
use std::{path::{Path, PathBuf}, str::FromStr};
use crate::error;
use crate::params::{NodeKeyParams, NodeKeyType};

/// The file name of the node's Ed25519 secret key inside the chain-specific
/// network config directory, if neither `--node-key` nor `--node-key-file`
/// is specified in combination with `--node-key-type=ed25519`.
const NODE_KEY_ED25519_FILE: &str = "secret_ed25519";

/// Check whether a node name is considered as valid
pub fn is_node_name_valid(_name: &str) -> Result<(), &str> {
	let name = _name.to_string();
	if name.chars().count() >= crate::NODE_NAME_MAX_LENGTH {
		return Err("Node name too long");
	}

	let invalid_chars = r"[\\.@]";
	let re = Regex::new(invalid_chars).unwrap();
	if re.is_match(&name) {
		return Err("Node name should not contain invalid chars such as '.' and '@'");
	}

	let invalid_patterns = r"(https?:\\/+)?(www)+";
	let re = Regex::new(invalid_patterns).unwrap();
	if re.is_match(&name) {
		return Err("Node name should not contain urls");
	}

	Ok(())
}

/// Create a `NodeKeyConfig` from the given `NodeKeyParams` in the context
/// of an optional network config storage directory.
pub fn node_key_config<P>(params: NodeKeyParams, net_config_dir: &Option<P>)
	-> error::Result<NodeKeyConfig>
where
	P: AsRef<Path>
{
	match params.node_key_type {
		NodeKeyType::Ed25519 =>
			params.node_key.as_ref().map(parse_ed25519_secret).unwrap_or_else(||
				Ok(params.node_key_file
					.or_else(|| net_config_file(net_config_dir, NODE_KEY_ED25519_FILE))
					.map(sc_network::config::Secret::File)
					.unwrap_or(sc_network::config::Secret::New)))
				.map(NodeKeyConfig::Ed25519)
	}
}

/// Create an error caused by an invalid node key argument.
fn invalid_node_key(e: impl std::fmt::Display) -> error::Error {
	error::Error::Input(format!("Invalid node key: {}", e))
}

/// Parse a Ed25519 secret key from a hex string into a `sc_network::Secret`.
fn parse_ed25519_secret(hex: &String) -> error::Result<sc_network::config::Ed25519Secret> {
	H256::from_str(&hex).map_err(invalid_node_key).and_then(|bytes|
		sc_network::config::identity::ed25519::SecretKey::from_bytes(bytes)
			.map(sc_network::config::Secret::Input)
			.map_err(invalid_node_key))
}

fn net_config_file<P>(net_config_dir: &Option<P>, name: &str) -> Option<PathBuf>
where
	P: AsRef<Path>
{
	net_config_dir.as_ref().map(|d| d.as_ref().join(name))
}

#[cfg(test)]
mod tests {
	use super::*;
	use sc_network::config::identity::ed25519;

	#[test]
	fn tests_node_name_good() {
		assert!(is_node_name_valid("short name").is_ok());
	}

	#[test]
	fn tests_node_name_bad() {
		assert!(is_node_name_valid("long names are not very cool for the ui").is_err());
		assert!(is_node_name_valid("Dots.not.Ok").is_err());
		assert!(is_node_name_valid("http://visit.me").is_err());
		assert!(is_node_name_valid("https://visit.me").is_err());
		assert!(is_node_name_valid("www.visit.me").is_err());
		assert!(is_node_name_valid("email@domain").is_err());
	}

	#[test]
	fn test_node_key_config_input() {
		fn secret_input(net_config_dir: Option<String>) -> error::Result<()> {
			NodeKeyType::variants().iter().try_for_each(|t| {
				let node_key_type = NodeKeyType::from_str(t).unwrap();
				let sk = match node_key_type {
					NodeKeyType::Ed25519 => ed25519::SecretKey::generate().as_ref().to_vec()
				};
				let params = NodeKeyParams {
					node_key_type,
					node_key: Some(format!("{:x}", H256::from_slice(sk.as_ref()))),
					node_key_file: None
				};
				node_key_config(params, &net_config_dir).and_then(|c| match c {
					NodeKeyConfig::Ed25519(sc_network::config::Secret::Input(ref ski))
						if node_key_type == NodeKeyType::Ed25519 &&
							&sk[..] == ski.as_ref() => Ok(()),
					_ => Err(error::Error::Input("Unexpected node key config".into()))
				})
			})
		}

		assert!(secret_input(None).is_ok());
		assert!(secret_input(Some("x".to_string())).is_ok());
	}

	#[test]
	fn test_node_key_config_file() {
		fn secret_file(net_config_dir: Option<String>) -> error::Result<()> {
			NodeKeyType::variants().iter().try_for_each(|t| {
				let node_key_type = NodeKeyType::from_str(t).unwrap();
				let tmp = tempfile::Builder::new().prefix("alice").tempdir()?;
				let file = tmp.path().join(format!("{}_mysecret", t)).to_path_buf();
				let params = NodeKeyParams {
					node_key_type,
					node_key: None,
					node_key_file: Some(file.clone())
				};
				node_key_config(params, &net_config_dir).and_then(|c| match c {
					NodeKeyConfig::Ed25519(sc_network::config::Secret::File(ref f))
						if node_key_type == NodeKeyType::Ed25519 && f == &file => Ok(()),
					_ => Err(error::Error::Input("Unexpected node key config".into()))
				})
			})
		}

		assert!(secret_file(None).is_ok());
		assert!(secret_file(Some("x".to_string())).is_ok());
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
				let typ = params.node_key_type;
				node_key_config::<String>(params, &None)
					.and_then(|c| match c {
						NodeKeyConfig::Ed25519(sc_network::config::Secret::New)
							if typ == NodeKeyType::Ed25519 => Ok(()),
						_ => Err(error::Error::Input("Unexpected node key config".into()))
					})
			})
		}

		fn some_config_dir(net_config_dir: String) -> error::Result<()> {
			with_def_params(|params| {
				let dir = PathBuf::from(net_config_dir.clone());
				let typ = params.node_key_type;
				node_key_config(params, &Some(net_config_dir.clone()))
					.and_then(move |c| match c {
						NodeKeyConfig::Ed25519(sc_network::config::Secret::File(ref f))
							if typ == NodeKeyType::Ed25519 &&
								f == &dir.join(NODE_KEY_ED25519_FILE) => Ok(()),
						_ => Err(error::Error::Input("Unexpected node key config".into()))
				})
			})
		}

		assert!(no_config_dir().is_ok());
		assert!(some_config_dir("x".to_string()).is_ok());
	}
}
