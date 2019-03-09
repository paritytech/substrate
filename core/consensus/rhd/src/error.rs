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
use consensus::error::{Error as CommonError, ErrorKind as CommonErrorKind};
use primitives::AuthorityId;
use client;
use error_chain::{error_chain, error_chain_processing, impl_error_chain_processed,
	impl_extract_backtrace, impl_error_chain_kind};

error_chain! {
	links {
		Client(client::error::Error, client::error::ErrorKind);
		Common(CommonError, CommonErrorKind);
	}
	errors {
		NotValidator(id: AuthorityId) {
			description("Local account ID not a validator at this block."),
			display("Local account ID ({:?}) not a validator at this block.", id),
		}
		PrematureDestruction {
			description("Proposer destroyed before finishing proposing or evaluating"),
			display("Proposer destroyed before finishing proposing or evaluating"),
		}
		Timer(e: ::tokio::timer::Error) {
			description("Failed to register or resolve async timer."),
			display("Timer failed: {}", e),
		}
		Executor(e: ::futures::future::ExecuteErrorKind) {
			description("Unable to dispatch agreement future"),
			display("Unable to dispatch agreement future: {:?}", e),
		}
	}
}

impl From<::rhododendron::InputStreamConcluded> for Error {
	fn from(_: ::rhododendron::InputStreamConcluded) -> Self {
		CommonErrorKind::IoTerminated.into()
	}
}

impl From<CommonErrorKind> for Error {
	fn from(e: CommonErrorKind) -> Self {
		CommonError::from(e).into()
	}
}
