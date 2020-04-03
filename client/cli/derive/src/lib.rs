// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! Configuration trait for a CLI based on substrate

#![deny(missing_docs)]

mod substrate_cli;

use proc_macro_error::proc_macro_error;

/// A procedural macro that helps implement SubstrateCli on an object. It will implement
/// automatically for you: impl_name (from the crate's name), impl_version (from the crate's
/// version, platform architecture and current commit of the Git repository), author (from the
/// crate's authors), description (from the crate's description) but you still need to implement the
/// support_url and the copyright_start_year yourself as those cannot be automatically found.
///
/// # Example
///
/// ```no_run
/// # use sc_cli_derive::substrate_cli;
/// #
/// struct MyCli {
///     shared: sc_cli::SharedParams,
///     import: sc_cli::ImportParams,
///     keystore: sc_cli::KeystoreParams,
/// }
///
/// #[substrate_cli(
///     support_url = "http://example.org",
///     copyright_start_year = 2020,
///     impl_version = "0.1.0",
/// )]
/// impl sc_cli::SubstrateCli for MyCli {
///     fn load_spec(&self, id: &str) -> Result<Box<dyn sc_service::ChainSpec>, String> {
///         unimplemented!()
///     }
/// }
/// ```
#[proc_macro_attribute]
#[proc_macro_error]
pub fn substrate_cli(
	a: proc_macro::TokenStream,
	i: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
	substrate_cli::substrate_cli(a, i).into()
}
