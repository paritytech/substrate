// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

//! Errors that can occur during the service operation.

use sc_network;
use sc_keystore;
use sp_consensus;
use sp_blockchain;

/// Service Result typedef.
pub type Result<T> = std::result::Result<T, Error>;

/// Service errors.
#[derive(Debug, derive_more::Display, derive_more::From)]
pub enum Error {
	/// Client error.
	Client(sp_blockchain::Error),
	/// IO error.
	Io(std::io::Error),
	/// Consensus error.
	Consensus(sp_consensus::Error),
	/// Network error.
	Network(sc_network::error::Error),
	/// Keystore error.
	Keystore(sc_keystore::Error),
	/// Best chain selection strategy is missing.
	#[display(fmt="Best chain selection strategy (SelectChain) is not provided.")]
	SelectChainRequired,
	/// Tasks executor is missing.
	#[display(fmt="Tasks executor hasn't been provided.")]
	TaskExecutorRequired,
	/// Other error.
	Other(String),
}

impl<'a> From<&'a str> for Error {
	fn from(s: &'a str) -> Self {
		Error::Other(s.into())
	}
}

impl From<prometheus_endpoint::PrometheusError> for Error {
	fn from(e: prometheus_endpoint::PrometheusError) -> Self {
		Error::Other(format!("Prometheus error: {}", e))
	}
}

impl std::error::Error for Error {
	fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
		match self {
			Error::Client(ref err) => Some(err),
			Error::Io(ref err) => Some(err),
			Error::Consensus(ref err) => Some(err),
			Error::Network(ref err) => Some(err),
			Error::Keystore(ref err) => Some(err),
			_ => None,
		}
	}
}
