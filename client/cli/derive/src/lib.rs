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
mod substrate_cli_params;
mod substrate_cli_config_wrapper;

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
///
/// ```
#[proc_macro_attribute]
#[proc_macro_error]
pub fn substrate_cli(
	a: proc_macro::TokenStream,
	i: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
	substrate_cli::substrate_cli(a, i).into()
}

/// A procedural macro that helps implement CliConfiguration on an object. If the object has any
/// of the standard fields SharedParams, ImportParams, NodeKeyParams, KeystoreParams,
/// PruningParams, then you can use this macro to automatically implement the functions that will
/// get the values from those *Params fields.
///
/// # Example
///
/// ```no_run
/// # use sc_cli_derive::substrate_cli_params;
/// #
/// struct MyCommand {
///     shared: sc_cli::SharedParams,
///     import: sc_cli::ImportParams,
///     keystore: sc_cli::KeystoreParams,
/// }
///
/// #[substrate_cli_params(
///     shared_params = shared,
///     import_params = import,
///     keystore_params = keystore,
/// )]
/// impl sc_cli::CliConfiguration for MyCommand {
///     fn is_dev(&self) -> sc_cli::Result<bool> {
///         // override: this function will be used preferably over the value in SharedParams
///         Ok(true)
///     }
/// }
/// ```
#[proc_macro_attribute]
#[proc_macro_error]
pub fn substrate_cli_params(
	a: proc_macro::TokenStream,
	i: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
	substrate_cli_params::substrate_cli_params(a, i).into()
}

/// A procedural macro that helps implement CliConfiguration on an object. If the object wraps
/// another object that implement CliConfiguration, use this macro to automatically create all the
/// functions that will call their parent function in the wrapped object. Every function defined in
/// this impl will have precedence over the function that is in the wrapped object.
///
/// # Example
///
/// ```no_run
/// # use sc_cli_derive::{substrate_cli_params, substrate_cli_config_wrapper};
/// #
/// # struct ExistingObject {
/// #     shared: sc_cli::SharedParams,
/// #     import: sc_cli::ImportParams,
/// #     keystore: sc_cli::KeystoreParams,
/// # }
/// #
/// # #[substrate_cli_params(shared_params = shared, import_params = import, keystore_params = keystore)]
/// # impl sc_cli::CliConfiguration for ExistingObject {}
/// #
/// struct Wrapper {
///     inner: ExistingObject,
/// }
///
/// #[substrate_cli_config_wrapper(inner)]
/// impl sc_cli::CliConfiguration for Wrapper {
///     fn is_dev(&self) -> sc_cli::Result<bool> {
///         // override
///         Ok(true)
///     }
/// }
/// ```
#[proc_macro_attribute]
#[proc_macro_error]
pub fn substrate_cli_config_wrapper(
	a: proc_macro::TokenStream,
	i: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
	substrate_cli_config_wrapper::substrate_cli_config_wrapper(a, i).into()
}
