#![allow(missing_docs)]

use sp_std::{prelude::*, fmt, result};

pub trait Error: fmt::Debug + fmt::Display {}

impl<T> Error for T where T: fmt::Debug + fmt::Display {}

#[derive(Debug)]
pub struct OffchainError(pub Box<dyn Error + Send>);

impl fmt::Display for OffchainError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{}", self.0)
	}
}

pub type Result<T> = result::Result<T, OffchainError>;
