// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Error types in the rhododendron Consensus service.
use consensus::error::{Error as CommonError};
use primitives::AuthorityId;
use client;

/// A result alias.
pub type Result<T> = std::result::Result<T, Error>;

/// A RHD error type.
#[derive(Debug, derive_more::Display, derive_more::From)]
pub enum Error {
	/// Client error.
	Client(client::error::Error),
	/// Consensus error.
	Common(CommonError),
	/// Local account ID not a validator at this block.
	#[display(fmt="Local account ID ({:?}) not a validator at this block.", _0)]
	NotValidator(AuthorityId),
	/// Proposer destroyed before finishing proposing or evaluating
	#[display(fmt="Proposer destroyed before finishing proposing or evaluating")]
	PrematureDestruction,
	/// Failed to register or resolve async timer.
	#[display(fmt="Timer failed: {}", _0)]
	Timer(tokio::timer::Error),
	/// Unable to dispatch agreement future
	#[display(fmt="Unable to dispatch agreement future: {:?}", _0)]
	Executor(futures::future::ExecuteErrorKind),
}

impl From<::rhododendron::InputStreamConcluded> for Error {
	fn from(_: ::rhododendron::InputStreamConcluded) -> Self {
		CommonError::IoTerminated.into()
	}
}
