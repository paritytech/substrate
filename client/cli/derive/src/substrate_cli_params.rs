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

use proc_macro_error::{abort, abort_call_site};
use quote::{quote, ToTokens};
use std::collections::{HashMap, HashSet};
use syn::parse::Parser;
use syn::{punctuated::Punctuated, spanned::Spanned, *};

macro_rules! define_if_missing {
	(
		$existing_methods:expr, $impl:expr, $path:ident,
		{ fn $method:ident ( &self $(, $arg:ident : $ty:ty)* $(,)? ) $(-> $result:ty)? }
	) => {
		if !$existing_methods.contains(stringify!($method)) {
			$impl.items.push(ImplItem::Verbatim(quote! {
				fn $method(&self, $($arg : $ty),*) $(-> $result)? {
					self.#$path.$method($($arg),*)
				}
			}));
		}
	}
}

pub(crate) fn substrate_cli_params(
	a: proc_macro::TokenStream,
	i: proc_macro::TokenStream,
) -> proc_macro2::TokenStream {
	let attrs = match Punctuated::<ExprAssign, Token![,]>::parse_terminated.parse(a) {
		Ok(x) => x,
		Err(err) => abort!(err.span(), "could not parse attributes: {}", err),
	};

	let mut attrs = attrs
		.iter()
		.map(|x| {
			(
				match &*x.left {
					Expr::Path(p) if p.path.segments.len() == 1 => {
						p.path.segments[0].ident.to_string()
					}
					_ => abort!(x.left.span(), "could not parse token"),
				},
				(*x.right).to_token_stream(),
			)
		})
		.collect::<HashMap<_, _>>();

	let shared_params = attrs.remove("shared_params");
	let import_params = attrs.remove("import_params");
	let pruning_params = attrs.remove("pruning_params").or_else(|| {
		import_params
			.as_ref()
			.map(|x| quote!(#x.pruning_params).into())
	});
	let keystore_params = attrs.remove("keystore_params");
	let network_params = attrs.remove("network_params");
	let node_key_params = attrs.remove("node_key_params").or_else(|| {
		network_params
			.as_ref()
			.map(|x| quote!(#x.node_key_params).into())
	});

	if !attrs.is_empty() {
		abort_call_site!(
			"unknown macro parameters: {}",
			attrs
				.keys()
				.map(|x| x.as_str())
				.collect::<Vec<_>>()
				.join(", ")
		);
	}

	let mut i: ItemImpl = match syn::parse(i) {
		Ok(x) => x,
		_ => abort_call_site!("this macro only works on an impl"),
	};

	let existing_methods = i
		.items
		.iter()
		.filter_map(|x| match x {
			ImplItem::Method(x) => Some(x.sig.ident.to_string()),
			_ => None,
		})
		.collect::<HashSet<_>>();

	if let Some(path) = shared_params {
		define_if_missing!(existing_methods, i, path, {
			fn base_path(&self)
			-> ::sc_cli::Result<::std::option::Option<::std::path::PathBuf>>
		});

		define_if_missing!(existing_methods, i, path, {
			fn is_dev(&self) -> ::sc_cli::Result<bool>
		});

		define_if_missing!(existing_methods, i, path, {
			fn chain_id(&self, is_dev: bool) -> ::sc_cli::Result<String>
		});

		define_if_missing!(existing_methods, i, path, {
			fn database_config(
				&self,
				base_path: &::std::path::PathBuf,
				cache_size: usize,
			) -> ::sc_cli::Result<::sc_service::config::DatabaseConfig>
		});

		if !existing_methods.contains("init") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn init<C: ::sc_cli::SubstrateCli>(&self) -> ::sc_cli::Result<()> {
					self.#path.init::<C>()
				}
			}));
		}
	}

	if let Some(path) = import_params {
		define_if_missing!(existing_methods, i, path, {
			fn tracing_receiver(&self) -> ::sc_cli::Result<::sc_service::TracingReceiver>
		});

		define_if_missing!(existing_methods, i, path, {
			fn tracing_targets(&self)
			-> ::sc_cli::Result<::std::option::Option<::std::string::String>>
		});

		define_if_missing!(existing_methods, i, path, {
			fn state_cache_size(&self) -> ::sc_cli::Result<usize>
		});

		define_if_missing!(existing_methods, i, path, {
			fn wasm_method(&self)
			-> ::sc_cli::Result<::sc_service::config::WasmExecutionMethod>
		});

		define_if_missing!(existing_methods, i, path, {
			fn execution_strategies(&self, is_dev: bool)
			-> ::sc_cli::Result<::sc_service::config::ExecutionStrategies>
		});

		define_if_missing!(existing_methods, i, path, {
			fn database_cache_size(&self) -> ::sc_cli::Result<::std::option::Option<usize>>
		});
	}

	if let Some(path) = pruning_params {
		define_if_missing!(existing_methods, i, path, {
			fn pruning(&self, is_dev: bool, roles: ::sc_service::Roles)
			-> ::sc_cli::Result<::sc_service::PruningMode>
		});
	}

	if let Some(path) = keystore_params {
		define_if_missing!(existing_methods, i, path, {
			fn keystore_config(&self, base_path: &::std::path::PathBuf)
			-> ::sc_cli::Result<::sc_service::config::KeystoreConfig>
		});
	}

	if let Some(path) = node_key_params {
		define_if_missing!(existing_methods, i, path, {
			fn node_key(&self, net_config_dir: &::std::path::PathBuf)
			-> ::sc_cli::Result<::sc_service::config::NodeKeyConfig>
		});
	}

	if let Some(path) = network_params {
		define_if_missing!(existing_methods, i, path, {
			fn network_config(
				&self,
				chain_spec: &std::boxed::Box<dyn ::sc_service::ChainSpec>,
				is_dev: bool,
				net_config_dir: &::std::path::PathBuf,
				client_id: &str,
				node_name: &str,
				node_key: ::sc_service::config::NodeKeyConfig,
			) -> ::sc_cli::Result<::sc_service::config::NetworkConfiguration>
		});
	}

	quote!(#i)
}
