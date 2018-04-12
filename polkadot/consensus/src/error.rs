// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Errors that can occur during the consensus process.

use primitives::block::{HeaderHash, Number};
error_chain! {
	links {
		PolkadotApi(::polkadot_api::Error, ::polkadot_api::ErrorKind);
		Bft(::bft::Error, ::bft::ErrorKind);
	}

	foreign_links {
		Io(::std::io::Error);
		SharedIo(::futures::future::SharedError<::std::io::Error>);
	}

	errors {
		InvalidDutyRosterLength(expected: usize, got: usize) {
			description("Duty Roster had invalid length"),
			display("Invalid duty roster length: expected {}, got {}", expected, got),
		}
		ProposalNotForPolkadot {
			description("Proposal provided not a Polkadot block."),
			display("Proposal provided not a Polkadot block."),
		}
		TimestampInFuture {
			description("Proposal had timestamp too far in the future."),
			display("Proposal had timestamp too far in the future."),
		}
		WrongParentHash(expected: HeaderHash, got: HeaderHash) {
			description("Proposal had wrong parent hash."),
			display("Proposal had wrong parent hash. Expected {:?}, got {:?}", expected, got),
		}
		WrongNumber(expected: Number, got: Number) {
			description("Proposal had wrong number."),
			display("Proposal had wrong number. Expected {:?}, got {:?}", expected, got),
		}
		ProposalTooLarge(size: usize) {
			description("Proposal exceeded the maximum size."),
			display(
				"Proposal exceeded the maximum size of {} by {} bytes.",
				::MAX_TRANSACTIONS_SIZE, ::MAX_TRANSACTIONS_SIZE.saturating_sub(*size)
			),
		}
		Executor(e: ::futures::future::ExecuteErrorKind) {
			description("Unable to dispatch agreement future"),
			display("Unable to dispatch agreement future: {:?}", e),
		}
	}
}

impl From<::bft::InputStreamConcluded> for Error {
	fn from(err: ::bft::InputStreamConcluded) -> Self {
		::bft::Error::from(err).into()
	}
}
