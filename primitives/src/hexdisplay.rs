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

//! Wrapper type for byte collections that outputs hex.

/// Simple wrapper to display hex representation of bytes.
pub struct HexDisplay<'a>(&'a [u8]);

impl<'a> HexDisplay<'a> {
	/// Create new instance that will display `d` as a hex string when displayed.
	pub fn from(d: &'a AsBytesRef) -> Self { HexDisplay(d.as_bytes_ref()) }
}

impl<'a> ::std::fmt::Display for HexDisplay<'a> {
	fn fmt(&self, fmtr: &mut ::std::fmt::Formatter) -> Result<(), ::std::fmt::Error> {
		for byte in self.0 {
			try!( fmtr.write_fmt(format_args!("{:02x}", byte)));
		}
		Ok(())
	}
}

/// Simple trait to transferm various types to `&[u8]`
pub trait AsBytesRef {
	/// Transferm `self` into `&[u8]`.
	fn as_bytes_ref(&self) -> &[u8];
}

impl<'a> AsBytesRef for &'a [u8] {
	fn as_bytes_ref(&self) -> &[u8] { self }
}

impl AsBytesRef for [u8] {
	fn as_bytes_ref(&self) -> &[u8] { &self }
}

impl AsBytesRef for Vec<u8> {
	fn as_bytes_ref(&self) -> &[u8] { &self }
}

macro_rules! impl_non_endians {
	( $( $t:ty ),* ) => { $(
		impl AsBytesRef for $t {
			fn as_bytes_ref(&self) -> &[u8] { &self[..] }
		}
	)* }
}

impl_non_endians!([u8; 1], [u8; 2], [u8; 3], [u8; 4], [u8; 5], [u8; 6], [u8; 7], [u8; 8],
	[u8; 10], [u8; 12], [u8; 14], [u8; 16], [u8; 20], [u8; 24], [u8; 28], [u8; 32], [u8; 40],
	[u8; 48], [u8; 56], [u8; 64], [u8; 80], [u8; 96], [u8; 112], [u8; 128]);
