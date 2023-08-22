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

use codec::{Decode, Encode};
use mixnet::core::PostErr;

/// Error handling a request. Sent in replies over the mixnet.
#[derive(Debug, thiserror::Error, Decode, Encode)]
pub enum RemoteErr {
	/// An error that doesn't map to any of the other variants.
	#[error("{0}")]
	Other(String),
	/// Failed to decode the request.
	#[error("Failed to decode the request: {0}")]
	Decode(String),
}

/// Mixnet error.
#[derive(Debug, thiserror::Error)]
pub enum Error {
	/// Failed to communicate with the mixnet service. Possibly it panicked. The node probably
	/// needs to be restarted.
	#[error(
		"Failed to communicate with the mixnet service; the node probably needs to be restarted"
	)]
	ServiceUnavailable,
	/// Did not receive a reply after the configured number of attempts.
	#[error("Did not receive a reply from the mixnet after the configured number of attempts")]
	NoReply,
	/// Received a malformed reply.
	#[error("Received a malformed reply from the mixnet")]
	BadReply,
	/// Failed to post the request to the mixnet. Note that some [`PostErr`] variants, eg
	/// [`PostErr::NotEnoughSpaceInQueue`], are handled internally and will never be returned from
	/// the top-level API.
	#[error("Failed to post the request to the mixnet: {0}")]
	Post(#[from] PostErr),
	/// Error reported by destination mixnode.
	#[error("Error reported by the destination mixnode: {0}")]
	Remote(#[from] RemoteErr),
}
