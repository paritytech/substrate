// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Error types in the BFT service.
use consensus_common::error::{Error as CommonError, ErrorKind as CommonErrorKind};

error_chain! {
	links {
		Common(CommonError, CommonErrorKind);
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
