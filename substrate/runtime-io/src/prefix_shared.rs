// Copyright 2018 Parity Technologies (UK) Ltd.
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

use codec::Decode;

/// Prefix length storage key.
pub const PREFIX_LEN_KEY: &'static [u8] = b":prefix_len";

/// Strips the prefix from the storage value.
pub fn strip_prefix(prefix_len_value: Option<Vec<u8>>, value: Vec<u8>) -> Result<(Option<Vec<u8>>, Option<Vec<u8>>), &'static str> {
	match parse_prefix_len(prefix_len_value)? {
		None => Ok((None, Some(value))),
		Some(prefix_len) if value.len() < prefix_len as usize =>
			Err("Too short storage value to have prefix"),
		Some(prefix_len) if value.len() == prefix_len as usize =>
			Ok((Some(value), None)),
		Some(prefix_len) => {
			let mut prefix = value;
			let value = prefix.split_off(prefix_len as usize);
			Ok((Some(prefix), Some(value)))
		},
	}
}

/// Parse prefix length value
pub fn parse_prefix_len(value: Option<Vec<u8>>) -> Result<Option<u32>, &'static str> {
	// prefix lenght is prefixed itself, but we do not know the length here
	// => the length is encoded as u32 and it is stored after the prefix
	// => read the u32 from the end and then check if the value is of correct length
	let value = match value {
		Some(value) => value,
		None => return Ok(None),
	};

	let value_len = value.len();
	match value_len {
		0 => Ok(None),
		_ if value_len < 4 => Err("Too short prefix length storage value"),
		_ => {
			let prefix_len: u32 = Decode::decode(&mut &value[value_len - 4..])
				.expect("passed 4-bytes slice to decode; 4 bytes are required to decode u32; qed");
			if value_len == prefix_len as usize + 4 {
				if prefix_len == 0 {
					Ok(None)
				} else {
					Ok(Some(prefix_len))
				}
			} else {
				Err("Invalid prefix length storage value")
			}
		}
	}
}

// This file is compiled by both susbtrate && runtime => to avoid duplicate tests execution:
// see tests in prefix.rs
