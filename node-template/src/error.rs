//! Initialization errors.

use client;

/// Initialization result.
pub type Result<T> = std::result::Result<T, Error>;

/// Initialization errors.
#[derive(Debug, derive_more::Display, derive_more::From)]
pub enum Error {
	/// IO error.
	Io(std::io::Error),
	/// CLI error.
	Cli(clap::Error),
	/// Client error.
	Client(client::error::Error),
}

impl std::error::Error for Error {}
