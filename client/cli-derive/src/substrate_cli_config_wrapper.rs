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

use proc_macro_error::abort_call_site;
use quote::quote;
use std::collections::HashSet;
use syn::*;

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

pub(crate) fn substrate_cli_config_wrapper(
	a: proc_macro::TokenStream,
	i: proc_macro::TokenStream,
) -> proc_macro2::TokenStream {
	let path = match syn::parse(a) {
		Ok(Expr::Path(x)) => x,
		_ => abort_call_site!("expected path to wrapped object"),
	};

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

	define_if_missing!(existing_methods, i, path, {
		fn base_path(&self) -> ::sc_cli::Result<::std::option::Option<::std::path::PathBuf>>
	});

	define_if_missing!(existing_methods, i, path, {
		fn is_dev(&self) -> ::sc_cli::Result<bool>
	});

	define_if_missing!(existing_methods, i, path, {
		fn roles(&self, is_dev: bool) -> ::sc_cli::Result<::sc_service::Roles>
	});

	define_if_missing!(existing_methods, i, path, {
		fn transaction_pool(&self) -> ::sc_cli::Result<::sc_service::TransactionPoolOptions>
	});

	define_if_missing!(existing_methods, i, path, {
		fn network_config(
			&self,
			chain_spec: &Box<dyn ::sc_service::ChainSpec>,
			is_dev: bool,
			base_path: &::std::path::PathBuf,
			client_id: &str,
			node_name: &str,
			node_key: ::sc_service::config::NodeKeyConfig,
		) -> ::sc_cli::Result<::sc_service::config::NetworkConfiguration>
	});

	define_if_missing!(existing_methods, i, path, {
		fn keystore_config(&self, base_path: &::std::path::PathBuf)
		-> ::sc_cli::Result<::sc_service::config::KeystoreConfig>
	});

	define_if_missing!(existing_methods, i, path, {
		fn database_cache_size(&self) -> ::sc_cli::Result<::std::option::Option<usize>>
	});

	define_if_missing!(existing_methods, i, path, {
		fn database_config(
			&self,
			base_path: &::std::path::PathBuf,
			cache_size: usize,
		) -> ::sc_cli::Result<::sc_service::config::DatabaseConfig>
	});

	define_if_missing!(existing_methods, i, path, {
		fn state_cache_size(&self) -> ::sc_cli::Result<usize>
	});

	define_if_missing!(existing_methods, i, path, {
		fn state_cache_child_ratio(&self) -> ::sc_cli::Result<::std::option::Option<usize>>
	});

	define_if_missing!(existing_methods, i, path, {
		fn pruning(&self, is_dev: bool, roles: ::sc_service::Roles)
		-> ::sc_cli::Result<::sc_service::config::PruningMode>
	});

	define_if_missing!(existing_methods, i, path, {
		fn chain_id(&self, is_dev: bool) -> ::sc_cli::Result<::std::string::String>
	});

	define_if_missing!(existing_methods, i, path, {
		fn node_name(&self) -> ::sc_cli::Result<::std::string::String>
	});

	define_if_missing!(existing_methods, i, path, {
		fn wasm_method(&self) -> ::sc_cli::Result<::sc_service::config::WasmExecutionMethod>
	});

	define_if_missing!(existing_methods, i, path, {
		fn execution_strategies(&self, is_dev: bool)
		-> ::sc_cli::Result<::sc_service::config::ExecutionStrategies>
	});

	define_if_missing!(existing_methods, i, path, {
		fn rpc_http(&self) -> ::sc_cli::Result<::std::option::Option<::std::net::SocketAddr>>
	});

	define_if_missing!(existing_methods, i, path, {
		fn rpc_ws(&self) -> ::sc_cli::Result<::std::option::Option<::std::net::SocketAddr>>
	});

	define_if_missing!(existing_methods, i, path, {
		fn rpc_ws_max_connections(&self)
		-> ::sc_cli::Result<::std::option::Option<usize>>
	});

	define_if_missing!(existing_methods, i, path, {
		fn rpc_cors(&self, is_dev: bool)
		-> ::sc_cli::Result<::std::option::Option<::std::vec::Vec<::std::string::String>>>
	});

	define_if_missing!(existing_methods, i, path, {
		fn prometheus_config(&self)
		-> ::sc_cli::Result<::std::option::Option<::sc_service::config::PrometheusConfig>>
	});

	define_if_missing!(existing_methods, i, path, {
		fn telemetry_endpoints(
			&self,
			chain_spec: &::std::boxed::Box<dyn ::sc_service::ChainSpec>,
		) -> ::sc_cli::Result<::std::option::Option<::sc_service::config::TelemetryEndpoints>>
	});

	define_if_missing!(existing_methods, i, path, {
		fn telemetry_external_transport(&self)
		-> ::sc_cli::Result<::std::option::Option<::sc_service::config::ExtTransport>>
	});

	define_if_missing!(existing_methods, i, path, {
		fn default_heap_pages(&self) -> ::sc_cli::Result<::std::option::Option<u64>>
	});

	define_if_missing!(existing_methods, i, path, {
		fn offchain_worker(&self, roles: ::sc_service::Roles) -> ::sc_cli::Result<bool>
	});

	define_if_missing!(existing_methods, i, path, {
		fn sentry_mode(&self) -> ::sc_cli::Result<bool>
	});

	define_if_missing!(existing_methods, i, path, {
		fn force_authoring(&self) -> ::sc_cli::Result<bool>
	});

	define_if_missing!(existing_methods, i, path, {
		fn disable_grandpa(&self) -> ::sc_cli::Result<bool>
	});

	define_if_missing!(existing_methods, i, path, {
		fn dev_key_seed(&self, is_dev: bool)
		-> ::sc_cli::Result<::std::option::Option<::std::string::String>>
	});

	define_if_missing!(existing_methods, i, path, {
		fn tracing_targets(&self)
		-> ::sc_cli::Result<::std::option::Option<::std::string::String>>
	});

	define_if_missing!(existing_methods, i, path, {
		fn tracing_receiver(&self) -> ::sc_cli::Result<::sc_service::TracingReceiver>
	});

	define_if_missing!(existing_methods, i, path, {
		fn node_key(&self, net_config_dir: &::std::path::PathBuf)
		-> ::sc_cli::Result<::sc_service::config::NodeKeyConfig>
	});

	define_if_missing!(existing_methods, i, path, {
		fn max_runtime_instances(&self) -> ::sc_cli::Result<::std::option::Option<usize>>
	});

	if !existing_methods.contains("init") {
		i.items.push(ImplItem::Verbatim(quote! {
			fn init<C: ::sc_cli::SubstrateCli>(&self) -> ::sc_cli::Result<()> {
				self.#path.init::<C>()
			}
		}));
	}

	quote!(#i)
}
