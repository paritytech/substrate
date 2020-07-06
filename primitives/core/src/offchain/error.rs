#![allow(missing_docs)]

use sp_std::{prelude::*, fmt, result};

#[derive(Debug)]
pub struct OffchainError(pub Box<dyn fmt::Debug + Send>);

impl fmt::Display for OffchainError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{:?}", self)
	}
}

#[cfg(std)]
impl From<std::error::Error> for OffchainError {
	fn from(err: std::error::Error) -> Self {
		OffchainError(Box::new(err))
	}
}

pub type Result<T> = result::Result<T, OffchainError>;
