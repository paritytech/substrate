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
	let missing = |method| !existing_methods.contains(method);

	if let Some(ident) = shared_params {
		if missing("base_path") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn base_path(&self) -> ::sc_cli::Result<::std::option::Option<&::std::path::PathBuf>> {
					Ok(self.#ident.base_path.as_ref())
				}
			}));
		}
		if missing("is_dev") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn is_dev(&self) -> ::sc_cli::Result<bool> {
					Ok(self.#ident.dev)
				}
			}));
		}
		if missing("chain_id") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn chain_id(&self, is_dev: bool) -> ::sc_cli::Result<String> {
					self.#ident.chain_id(is_dev)
				}
			}));
		}
		if missing("database_config") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn database_config(
					&self,
					base_path: &::std::path::PathBuf,
					cache_size: ::std::option::Option<usize>,
				) -> ::sc_cli::Result<::sc_service::config::DatabaseConfig> {
					Ok(self.#ident.database_config(base_path, cache_size))
				}
			}));
		}
		if missing("init") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn init<C: ::sc_cli::SubstrateCLI>(&self) -> ::sc_cli::Result<()> {
					self.#ident.init::<C>()
				}
			}));
		}
	}

	if let Some(ident) = import_params {
		if missing("tracing_receiver") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn tracing_receiver(&self) -> ::sc_cli::Result<::sc_service::TracingReceiver> {
					Ok(self.#ident.tracing_receiver.clone().into())
				}
			}));
		}
		if missing("tracing_targets") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn tracing_targets(&self) -> ::sc_cli::Result<::std::option::Option<::std::string::String>> {
					Ok(self.#ident.tracing_targets.clone().into())
				}
			}));
		}
		if missing("state_cache_size") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn state_cache_size(&self) -> ::sc_cli::Result<usize> {
					Ok(self.#ident.state_cache_size)
				}
			}));
		}
		if missing("wasm_method") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn wasm_method(&self) -> ::sc_cli::Result<::sc_service::config::WasmExecutionMethod> {
					Ok(self.#ident.wasm_method())
				}
			}));
		}
		if missing("execution_strategies") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn execution_strategies(&self, is_dev: bool) -> ::sc_cli::Result<::sc_service::config::ExecutionStrategies> {
					self.#ident.execution_strategies(is_dev)
				}
			}));
		}
		if missing("database_cache_size") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn database_cache_size(&self) -> ::sc_cli::Result<::std::option::Option<usize>> {
					Ok(self.#ident.database_cache_size)
				}
			}));
		}
	}

	if let Some(ident) = pruning_params {
		if missing("pruning") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn pruning(&self, is_dev: bool, roles: ::sc_service::Roles) -> ::sc_cli::Result<::sc_service::PruningMode> {
					self.#ident.pruning(roles, is_dev)
				}
			}));
		}
	}

	if let Some(ident) = keystore_params {
		if missing("keystore_config") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn keystore_config(&self, base_path: &::std::path::PathBuf)
				-> ::sc_cli::Result<::sc_service::config::KeystoreConfig> {
					self.#ident.keystore_config(base_path)
				}
			}));
		}
	}

	if let Some(ident) = node_key_params {
		if missing("keystore_config") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn node_key(&self, net_config_dir: &::std::path::PathBuf)
				-> ::sc_cli::Result<::sc_service::config::NodeKeyConfig> {
					self.#ident.node_key(net_config_dir)
				}
			}));
		}
	}

	if let Some(ident) = network_params {
		if missing("network_config") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn network_config(
					&self,
					chain_spec: &Box<dyn ::sc_service::ChainSpec>,
					is_dev: bool,
					base_path: &::std::path::PathBuf,
					client_id: &str,
					node_name: &str,
					node_key: ::sc_service::config::NodeKeyConfig,
				) -> ::sc_cli::Result<::sc_service::config::NetworkConfiguration> {
					self.#ident
						.network_config(chain_spec, client_id, is_dev, base_path, node_name, node_key)
				}
			}));
		}
	}

	quote!(#i)
}
