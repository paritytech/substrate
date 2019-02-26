// Copyright 2015-2017 Parity Technologies
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
/// Error concerning the Parity-Codec based decoder.
pub enum Error {
	/// Bad format.
	BadFormat,
}

#[cfg(feature="std")]
impl StdError for Error {
	fn description(&self) -> &str {
		"codec error"
	}
}

#[cfg(feature="std")]
impl fmt::Display for Error {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		fmt::Debug::fmt(&self, f)
	}
}
