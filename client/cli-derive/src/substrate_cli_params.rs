use proc_macro;
use proc_macro_error::{abort, abort_call_site};
use quote::{quote, ToTokens};
use std::collections::{HashMap, HashSet};
use syn;
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
	let pruning_params = attrs.remove("pruning_params").or_else(|| import_params.as_ref().map(|x| quote!(#x.pruning_params).into()));
	let keystore_params = attrs.remove("keystore_params");
	let network_params = attrs.remove("network_params");
	let node_key_params = attrs.remove("node_key_params").or_else(|| network_params.as_ref().map(|x| quote!(#x.node_key_params).into()));

	if !attrs.is_empty() {
		abort_call_site!("unknown macro parameters: {}", attrs.keys().map(|x| x.as_str()).collect::<Vec<_>>().join(", "));
	}

	let mut i: ItemImpl = match syn::parse(i) {
		Ok(x) => x,
		_ => abort_call_site!("this macro only works on an impl"),
	};

	let existing_methods = i.items.iter().filter_map(|x| match x {
		ImplItem::Method(x) => Some(x.sig.ident.to_string()),
		_ => None,
	})
    	.collect::<HashSet<_>>();
	let missing = |method| !existing_methods.contains(method);

	if let Some(ident) = shared_params {
		if missing("get_base_path") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn get_base_path(&self) -> ::sc_cli::Result<::std::option::Option<&::std::path::PathBuf>> {
					Ok(self.#ident.base_path.as_ref())
				}
			}));
		}
		if missing("is_dev") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn is_dev(&self) -> bool {
					self.#ident.dev
				}
			}));
		}
		if missing("get_chain_spec") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn get_chain_spec<C: ::sc_cli::SubstrateCLI<G, E>, G, E>(&self) -> ::sc_cli::Result<::sc_service::ChainSpec<G, E>>
				where
					G: ::sc_service::RuntimeGenesis,
					E: ::sc_service::ChainSpecExtension,
				{
					self.#ident.get_chain_spec::<C, G, E>()
				}
			}));
		}
		if missing("get_database_config") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn get_database_config(
					&self,
					base_path: &::std::path::PathBuf,
					cache_size: ::std::option::Option<usize>,
				) -> ::sc_cli::Result<::sc_service::config::DatabaseConfig> {
					Ok(self.#ident.get_database_config(base_path, cache_size))
				}
			}));
		}
		if missing("init") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn init<C: ::sc_cli::SubstrateCLI<G, E>, G, E>(&self) -> ::sc_cli::Result<()>
				where
					G: ::sc_service::RuntimeGenesis,
					E: ::sc_service::ChainSpecExtension,
				{
					self.#ident.init::<C, G, E>()
				}
			}));
		}
	}

	if let Some(ident) = import_params {
		if missing("get_tracing_receiver") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn get_tracing_receiver(&self) -> ::sc_cli::Result<::sc_service::TracingReceiver> {
					Ok(self.#ident.tracing_receiver.clone().into())
				}
			}));
		}
		if missing("get_tracing_targets") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn get_tracing_targets(&self) -> ::sc_cli::Result<::std::option::Option<::std::string::String>> {
					Ok(self.#ident.tracing_targets.clone().into())
				}
			}));
		}
		if missing("get_state_cache_size") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn get_state_cache_size(&self) -> ::sc_cli::Result<usize> {
					Ok(self.#ident.state_cache_size)
				}
			}));
		}
		if missing("get_wasm_method") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn get_wasm_method(&self) -> ::sc_cli::Result<::sc_service::config::WasmExecutionMethod> {
					Ok(self.#ident.get_wasm_method())
				}
			}));
		}
		if missing("get_execution_strategies") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn get_execution_strategies(&self, is_dev: bool) -> ::sc_cli::Result<::sc_service::config::ExecutionStrategies> {
					self.#ident.get_execution_strategies(is_dev)
				}
			}));
		}
		if missing("get_database_cache_size") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn get_database_cache_size(&self) -> ::sc_cli::Result<::std::option::Option<usize>> {
					Ok(self.#ident.database_cache_size)
				}
			}));
		}
	}

	if let Some(ident) = pruning_params {
		if missing("get_pruning") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn get_pruning(&self, is_dev: bool, roles: ::sc_service::Roles) -> ::sc_cli::Result<::sc_service::PruningMode> {
					self.#ident.get_pruning(roles, is_dev)
				}
			}));
		}
	}

	if let Some(ident) = keystore_params {
		if missing("get_keystore_config") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn get_keystore_config(&self, base_path: &::std::path::PathBuf)
				-> ::sc_cli::Result<::sc_service::config::KeystoreConfig> {
					self.#ident.get_keystore_config(base_path)
				}
			}));
		}
	}

	if let Some(ident) = node_key_params {
		if missing("get_keystore_config") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn get_node_key(&self, net_config_dir: &::std::path::PathBuf)
				-> ::sc_cli::Result<::sc_network::config::NodeKeyConfig> {
					self.#ident.get_node_key(net_config_dir)
				}
			}));
		}
	}

	if let Some(ident) = network_params {
		if missing("get_network_config") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn get_network_config<G, E>(
					&self,
					chain_spec: &::sc_service::ChainSpec<G, E>,
					is_dev: bool,
					base_path: &::std::path::PathBuf,
					client_id: &str,
					node_name: &str,
					node_key: ::sc_network::config::NodeKeyConfig,
				) -> ::sc_cli::Result<::sc_service::config::NetworkConfiguration>
				where
					G: ::sc_service::RuntimeGenesis,
					E: ::sc_service::ChainSpecExtension,
				{
					self.#ident
						.get_network_config(chain_spec, client_id, is_dev, base_path, node_name, node_key)
				}
			}));
		}
	}

	quote!(#i)
}
