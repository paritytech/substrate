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

use std::fmt;

use serde::{de, Serializer, Deserializer};

/// Serializes a slice of bytes into a most compact form.
pub fn serialize<S>(bytes: &[u8], serializer: S) -> Result<S::Ok, S::Error> where
	S: Serializer,
{
	let hex = ::rustc_hex::ToHex::to_hex(bytes);
	serializer.serialize_str(&format!("0x{}", hex))
}

pub fn serialize_compact<S>(bytes: &[u8], serializer: S) -> Result<S::Ok, S::Error> where
	S: Serializer,
{
	let mut non_zero = bytes.len();
	for (i, b) in bytes.iter().enumerate() {
		if *b != 0 {
			non_zero = i;
			break;
		}
	}

	if non_zero == bytes.len() {
		return serializer.serialize_str("0x0");
	}

	let hex = ::rustc_hex::ToHex::to_hex(&bytes[non_zero..]);
	let has_leading_zero = !hex.is_empty() && &hex[0..1] == "0";
	return serializer.serialize_str(&format!("0x{}", if has_leading_zero { &hex[1..] } else { &hex }));
}

pub fn deserialize<'de, D>(deserializer: D) -> Result<Vec<u8>, D::Error> where
	D: Deserializer<'de>,
{
	deserialize_with_check(deserializer, |_| Ok(()))
}

pub fn deserialize_with_check<'de, D, F>(deserializer: D, check: F) -> Result<Vec<u8>, D::Error> where
	D: Deserializer<'de>,
	F: Fn(&str) -> Result<(), ErrorKind>,
{
	struct Visitor<F> {
		check: F,
	}

	impl<'a, F> de::Visitor<'a> for Visitor<F> where
		F: Fn(&str) -> Result<(), ErrorKind>,
	{
		type Value = Vec<u8>;

		fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
			write!(formatter, "a 0x-prefixed hex string")
		}

		fn visit_str<E: de::Error>(self, v: &str) -> Result<Self::Value, E> {
			if v.len() < 2  || &v[0..2] != "0x" {
				return Err(E::custom("prefix is missing"))
			}

			(self.check)(v).map_err(|err| match err {
				ErrorKind::InvalidLength(len) => E::invalid_length(len, &self),
			})?;

			let v = if v.len() % 2 == 0 { v[2..].to_owned() } else { format!("0{}", &v[2..]) };
			let bytes = ::rustc_hex::FromHex::from_hex(v.as_str())
				.map_err(|e| E::custom(&format!("invalid hex value: {:?}", e)))?;
			Ok(bytes)
		}

		fn visit_string<E: de::Error>(self, v: String) -> Result<Self::Value, E> {
			self.visit_str(&v)
		}
	}
	// TODO [ToDr] Use raw bytes if we switch to RLP / binencoding
	// (visit_bytes, visit_bytes_buf)
	deserializer.deserialize_str(Visitor { check })
}

pub enum ErrorKind {
	InvalidLength(usize),
}

