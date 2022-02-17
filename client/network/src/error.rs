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

//! Substrate network possible errors.

use crate::config::TransportConfig;
use libp2p::{Multiaddr, PeerId};

use std::{borrow::Cow, fmt};

/// Result type alias for the network.
pub type Result<T> = std::result::Result<T, Error>;

/// Error type for the network.
#[derive(derive_more::Display, derive_more::From)]
pub enum Error {
	/// Io error
	Io(std::io::Error),
	/// Client error
	Client(Box<sp_blockchain::Error>),
	/// The same bootnode (based on address) is registered with two different peer ids.
	#[display(
		fmt = "The same bootnode (`{}`) is registered with two different peer ids: `{}` and `{}`",
		address,
		first_id,
		second_id
	)]
	DuplicateBootnode {
		/// The address of the bootnode.
		address: Multiaddr,
		/// The first peer id that was found for the bootnode.
		first_id: PeerId,
		/// The second peer id that was found for the bootnode.
		second_id: PeerId,
	},
	/// Prometheus metrics error.
	Prometheus(prometheus_endpoint::PrometheusError),
	/// The network addresses are invalid because they don't match the transport.
	#[display(
		fmt = "The following addresses are invalid because they don't match the transport: {:?}",
		addresses
	)]
	AddressesForAnotherTransport {
		/// Transport used.
		transport: TransportConfig,
		/// The invalid addresses.
		addresses: Vec<Multiaddr>,
	},
	/// The same request-response protocol has been registered multiple times.
	#[display(fmt = "Request-response protocol registered multiple times: {}", protocol)]
	DuplicateRequestResponseProtocol {
		/// Name of the protocol registered multiple times.
		protocol: Cow<'static, str>,
	},
}

// Make `Debug` use the `Display` implementation.
impl fmt::Debug for Error {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		fmt::Display::fmt(self, f)
	}
}

impl std::error::Error for Error {
	fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
		match self {
			Self::Io(ref err) => Some(err),
			Self::Client(ref err) => Some(err),
			Self::Prometheus(ref err) => Some(err),
			Self::DuplicateBootnode { .. } |
			Self::AddressesForAnotherTransport { .. } |
			Self::DuplicateRequestResponseProtocol { .. } => None,
		}
	}
}
