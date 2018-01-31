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

//! Testing helpers.

use primitives::AccountID;
use super::statichex::StaticHexInto;

#[macro_export]
macro_rules! map {
	($( $name:expr => $value:expr ),*) => (
		vec![ $( ( $name, $value ) ),* ].into_iter().collect()
	)
}

/// One account (to which we know the secret key).
pub fn one() -> AccountID {
	"2f8c6129d816cf51c374bc7f08c3e63ed156cf78aefb4a6550d97b87997977ee".convert()
}
/// Another account (secret key known).
pub fn two() -> AccountID {
	"d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a".convert()
}

/// Hex display, this time for no_std. See main codebase for documentation.
pub struct HexDisplay<'a>(&'a [u8]);

impl<'a> HexDisplay<'a> {
	/// See main codebase for documentation.
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

/// See main codebase for documentation.
pub trait AsBytesRef {
	/// See main codebase for documentation.
	fn as_bytes_ref(&self) -> &[u8];
}

impl AsBytesRef for [u8] {
	fn as_bytes_ref(&self) -> &[u8] { &self }
}

impl<'a> AsBytesRef for &'a[u8] {
	fn as_bytes_ref(&self) -> &[u8] { self }
}

impl AsBytesRef for Vec<u8> {
	fn as_bytes_ref(&self) -> &[u8] { &self[..] }
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
