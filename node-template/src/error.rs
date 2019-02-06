//! Initialization errors.

use client;

error_chain! {
	foreign_links {
		Io(::std::io::Error) #[doc="IO error"];
		Cli(::clap::Error) #[doc="CLI error"];
	}
	links {
		Client(client::error::Error, client::error::ErrorKind) #[doc="Client error"];
	}
}
