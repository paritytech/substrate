// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

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
