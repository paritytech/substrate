// Copyright 2018 Parity Technologies (UK) Ltd.
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

use crate::NetworkConfiguration;
use libp2p::secio;
use log::{trace, warn};
use rand::Rng;
use std::io::{Error as IoError, ErrorKind as IoErrorKind, Read, Write};
use std::{fs, path::Path};

// File where the private key is stored.
const SECRET_FILE: &str = "secret";

/// Obtains or generates the local private key using the configuration.
pub fn obtain_private_key_from_config(
	config: &NetworkConfiguration
) -> Result<secio::SecioKeyPair, IoError> {
	obtain_private_key(&config.use_secret, &config.net_config_path)
}

/// Obtains or generates the local private key using the configuration.
pub fn obtain_private_key(
	secret: &Option<[u8; 32]>,
	net_config_path: &Option<String>,
) -> Result<secio::SecioKeyPair, IoError> {
	if let Some(ref secret) = secret {
		// Key was specified in the configuration.
		secio::SecioKeyPair::secp256k1_raw_key(&secret[..])
			.map_err(|err| IoError::new(IoErrorKind::InvalidData, err))
	} else {
		if let Some(ref path) = net_config_path {
			// Try fetch the key from a the file containing the secret.
			let secret_path = Path::new(path).join(SECRET_FILE);
			match load_private_key_from_file(&secret_path) {
				Ok(s) => Ok(s),
				Err(err) => {
					// Failed to fetch existing file ; generate a new key
					trace!(target: "sub-libp2p",
						"Failed to load existing secret key file {:?}, generating new key ; err = {:?}",
						secret_path,
						err
					);
					Ok(gen_key_and_try_write_to_file(&secret_path))
				}
			}

		} else {
			// No path in the configuration, nothing we can do except generate
			// a new key.
			let mut key: [u8; 32] = [0; 32];
			rand::rngs::EntropyRng::new().fill(&mut key);
			Ok(secio::SecioKeyPair::secp256k1_raw_key(&key)
				.expect("randomly-generated key with correct len should always be valid"))
		}
	}
}

/// Tries to load a private key from a file located at the given path.
fn load_private_key_from_file<P>(path: P)
	-> Result<secio::SecioKeyPair, IoError>
	where P: AsRef<Path> {
	fs::File::open(path)
		.and_then(|mut file| {
			// We are in 2018 and there is still no method on `std::io::Read`
			// that directly returns a `Vec`.
			let mut buf = Vec::new();
			file.read_to_end(&mut buf).map(|_| buf)
		})
		.and_then(|content|
			secio::SecioKeyPair::secp256k1_raw_key(&content)
				.map_err(|err| IoError::new(IoErrorKind::InvalidData, err))
		)
}

/// Generates a new secret key and tries to write it to the given file.
/// Doesn't error if we couldn't open or write to the file.
fn gen_key_and_try_write_to_file<P>(path: P) -> secio::SecioKeyPair
	where P: AsRef<Path> {
	let raw_key: [u8; 32] = rand::rngs::EntropyRng::new().gen();
	let secio_key = secio::SecioKeyPair::secp256k1_raw_key(&raw_key)
		.expect("randomly-generated key with correct len should always be valid");

	// And store the newly-generated key in the file if possible.
	// Errors that happen while doing so are ignored.
	match open_priv_key_file(&path) {
		Ok(mut file) =>
			match file.write_all(&raw_key) {
				Ok(()) => (),
				Err(err) => warn!(target: "sub-libp2p",
					"Failed to write secret key in file {:?} ; err = {:?}",
					path.as_ref(),
					err
				),
			},
		Err(err) => warn!(target: "sub-libp2p",
			"Failed to store secret key in file {:?} ; err = {:?}",
			path.as_ref(),
			err
		),
	}

	secio_key
}

/// Opens a file containing a private key in write mode.
#[cfg(unix)]
fn open_priv_key_file<P>(path: P) -> Result<fs::File, IoError>
	where P: AsRef<Path> {
	use std::os::unix::fs::OpenOptionsExt;
	fs::OpenOptions::new()
		.write(true)
		.create_new(true)
		.mode(256 | 128)		// 0o600 in decimal
		.open(path)
}
/// Opens a file containing a private key in write mode.
#[cfg(not(unix))]
fn open_priv_key_file<P>(path: P) -> Result<fs::File, IoError>
	where P: AsRef<Path> {
	fs::OpenOptions::new()
		.write(true)
		.create_new(true)
		.open(path)
}
