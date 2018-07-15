// Copyright 2015-2018 Parity Technologies (UK) Ltd.
// This file is part of Parity.

// Parity is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Parity is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Parity.  If not, see <http://www.gnu.org/licenses/>.

use std::{io, net, fmt};
use libc::{ENFILE, EMFILE};
use io::IoError;
use ethkey;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum DisconnectReason
{
	DisconnectRequested,
	TCPError,
	BadProtocol,
	UselessPeer,
	TooManyPeers,
	DuplicatePeer,
	IncompatibleProtocol,
	NullIdentity,
	ClientQuit,
	UnexpectedIdentity,
	LocalIdentity,
	PingTimeout,
	Unknown,
}

impl DisconnectReason {
	pub fn from_u8(n: u8) -> DisconnectReason {
		match n {
			0 => DisconnectReason::DisconnectRequested,
			1 => DisconnectReason::TCPError,
			2 => DisconnectReason::BadProtocol,
			3 => DisconnectReason::UselessPeer,
			4 => DisconnectReason::TooManyPeers,
			5 => DisconnectReason::DuplicatePeer,
			6 => DisconnectReason::IncompatibleProtocol,
			7 => DisconnectReason::NullIdentity,
			8 => DisconnectReason::ClientQuit,
			9 => DisconnectReason::UnexpectedIdentity,
			10 => DisconnectReason::LocalIdentity,
			11 => DisconnectReason::PingTimeout,
			_ => DisconnectReason::Unknown,
		}
	}
}

impl fmt::Display for DisconnectReason {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use self::DisconnectReason::*;

		let msg = match *self {
			DisconnectRequested => "disconnect requested",
			TCPError => "TCP error",
			BadProtocol => "bad protocol",
			UselessPeer => "useless peer",
			TooManyPeers => "too many peers",
			DuplicatePeer => "duplicate peer",
			IncompatibleProtocol => "incompatible protocol",
			NullIdentity => "null identity",
			ClientQuit => "client quit",
			UnexpectedIdentity => "unexpected identity",
			LocalIdentity => "local identity",
			PingTimeout => "ping timeout",
			Unknown => "unknown",
		};

		f.write_str(msg)
	}
}

error_chain! {
	foreign_links {
		SocketIo(IoError) #[doc = "Socket IO error."];
	}

	errors {
		#[doc = "Error concerning the network address parsing subsystem."]
		AddressParse {
			description("Failed to parse network address"),
			display("Failed to parse network address"),
		}

		#[doc = "Error concerning the network address resolution subsystem."]
		AddressResolve(err: Option<io::Error>) {
			description("Failed to resolve network address"),
			display("Failed to resolve network address {}", err.as_ref().map_or("".to_string(), |e| e.to_string())),
		}

		#[doc = "Authentication failure"]
		Auth {
			description("Authentication failure"),
			display("Authentication failure"),
		}

		#[doc = "Unrecognised protocol"]
		BadProtocol {
			description("Bad protocol"),
			display("Bad protocol"),
		}

		#[doc = "Expired message"]
		Expired {
			description("Expired message"),
			display("Expired message"),
		}

		#[doc = "Peer not found"]
		PeerNotFound {
			description("Peer not found"),
			display("Peer not found"),
		}

		#[doc = "Peer is disconnected"]
		Disconnect(reason: DisconnectReason) {
			description("Peer disconnected"),
			display("Peer disconnected: {}", reason),
		}

		#[doc = "Invalid node id"]
		InvalidNodeId {
			description("Invalid node id"),
			display("Invalid node id"),
		}

		#[doc = "Packet size is over the protocol limit"]
		OversizedPacket {
			description("Packet is too large"),
			display("Packet is too large"),
		}

		#[doc = "Reached system resource limits for this process"]
		ProcessTooManyFiles {
			description("Too many open files in process."),
			display("Too many open files in this process. Check your resource limits and restart parity"),
		}

		#[doc = "Reached system wide resource limits"]
		SystemTooManyFiles {
			description("Too many open files on system."),
			display("Too many open files on system. Consider closing some processes/release some file handlers or increas the system-wide resource limits and restart parity."),
		}

		#[doc = "An unknown IO error occurred."]
		Io(err: io::Error) {
			description("IO Error"),
			display("Unexpected IO error: {}", err),
		}
	}
}

impl From<io::Error> for Error {
	fn from(err: io::Error) -> Self {
		match err.raw_os_error() {
			Some(ENFILE) => ErrorKind::ProcessTooManyFiles.into(),
			Some(EMFILE) => ErrorKind::SystemTooManyFiles.into(),
			_ => Error::from_kind(ErrorKind::Io(err))
		}
	}
}

impl From<ethkey::Error> for Error {
	fn from(_err: ethkey::Error) -> Self {
		ErrorKind::Auth.into()
	}
}

impl From<ethkey::crypto::Error> for Error {
	fn from(_err: ethkey::crypto::Error) -> Self {
		ErrorKind::Auth.into()
	}
}

impl From<net::AddrParseError> for Error {
	fn from(_err: net::AddrParseError) -> Self { ErrorKind::AddressParse.into() }
}

#[test]
fn test_errors() {
	assert_eq!(DisconnectReason::ClientQuit, DisconnectReason::from_u8(8));
	let mut r = DisconnectReason::DisconnectRequested;
	for i in 0 .. 20 {
		r = DisconnectReason::from_u8(i);
	}
	assert_eq!(DisconnectReason::Unknown, r);
}

#[test]
fn test_io_errors() {
	use libc::{EMFILE, ENFILE};

	assert_matches!(
		<Error as From<io::Error>>::from(
			io::Error::from_raw_os_error(ENFILE)
			).kind(),
		ErrorKind::ProcessTooManyFiles);

	assert_matches!(
		<Error as From<io::Error>>::from(
			io::Error::from_raw_os_error(EMFILE)
			).kind(),
		ErrorKind::SystemTooManyFiles);

	assert_matches!(
		<Error as From<io::Error>>::from(
			io::Error::from_raw_os_error(0)
			).kind(),
		ErrorKind::Io(_));
}
