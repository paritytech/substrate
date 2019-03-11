// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Substrate customizable serde serializer.
//!
//! The idea is that we can later change the implementation
//! to something more compact, but for now we're using JSON.

#![warn(missing_docs)]

pub use serde_json::{from_str, from_slice, from_reader, Result, Error};

const PROOF: &str = "Serializers are infallible; qed";

/// Serialize the given data structure as a pretty-printed String of JSON.
pub fn to_string_pretty<T: serde::Serialize + ?Sized>(value: &T) -> String {
	serde_json::to_string_pretty(value).expect(PROOF)
}

/// Serialize the given data structure as a JSON byte vector.
pub fn encode<T: serde::Serialize + ?Sized>(value: &T) -> Vec<u8> {
	serde_json::to_vec(value).expect(PROOF)
}

/// Serialize the given data structure as JSON into the IO stream.
pub fn to_writer<W: ::std::io::Write, T: serde::Serialize + ?Sized>(writer: W, value: &T) -> Result<()> {
	serde_json::to_writer(writer, value)
}
