// Copyright 2015-2020 Parity Technologies (UK) Ltd.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#[cfg(feature="std")]
use std::fmt;
#[cfg(feature="std")]
use std::error::Error as StdError;

#[derive(Debug, PartialEq, Eq, Clone)]
/// Error for trie node decoding.
pub enum Error {
	/// Bad format.
	BadFormat,
	/// Decoding error.
	Decode(codec::Error)
}

impl From<codec::Error> for Error {
	fn from(x: codec::Error) -> Self {
		Error::Decode(x)
	}
}

#[cfg(feature="std")]
impl StdError for Error {
	fn description(&self) -> &str {
		match self {
			Error::BadFormat => "Bad format error",
			Error::Decode(_) => "Decoding error",
		}
	}
}

#[cfg(feature="std")]
impl fmt::Display for Error {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Error::Decode(e) => write!(f, "Decode error: {}", e.what()),
			Error::BadFormat => write!(f, "Bad format"),
		}
	}
}
