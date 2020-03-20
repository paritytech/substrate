use proc_macro;
use proc_macro_error::{abort_call_site};
use proc_macro2::{TokenStream};
use quote::quote;
use syn;
use syn::*;

macro_rules! match_and_call {
	(
		$enum:expr;
		$variants:expr;
		fn $method:ident ( &self $(, $arg:ident : $ty:ty)* $(,)? ) $(-> $result:ty)?
	) => {{
		let enum_ident = &$enum;
		let arms = $variants
			.iter()
			.map(|x| quote! {
				#enum_ident::#x(cmd) => cmd.$method($($arg),*),
			});

		quote! {
			fn $method (&self, $($arg : $ty),*) $(-> $result)? {
				match self {
					#( #arms )*
				}
			}
		}
	}};

	(
		$enum:expr;
		$variants:expr;
		fn $method:ident <C: ::sc_cli::SubstrateCLI<G, E>, G, E> ( &self $(, $arg:ident : $ty:ty)* $(,)? ) $(-> $result:ty)?
		where
			G: ::sc_service::RuntimeGenesis,
			E: ::sc_service::ChainSpecExtension $(,)?
	) => {{
		let enum_ident = &$enum;
		let arms = $variants
			.iter()
			.map(|x| quote! {
				#enum_ident::#x(cmd) => cmd.$method::<C, G, E>($($arg),*),
			});

		quote! {
			fn $method <C: ::sc_cli::SubstrateCLI<G, E>, G, E> (&self, $($arg : $ty),*) $(-> $result)?
			where
				G: ::sc_service::RuntimeGenesis,
				E: ::sc_service::ChainSpecExtension,
			{
				match self {
					#( #arms )*
				}
			}
		}
	}};
}

pub(crate) fn substrate_cli_subcommands(
	i: proc_macro::TokenStream,
) -> TokenStream {
	let i: DeriveInput = syn::parse(i).unwrap();

	let e = match &i.data {
		Data::Enum(x) => x,
		_ => abort_call_site!("this derive only works on an enum"),
	};

	let name = i.ident;
	let variants = e.variants.iter().map(|x| &x.ident).collect::<Vec<_>>();

	let methods = vec![

		match_and_call! {
			name;
			variants;
			fn get_base_path(&self) -> ::sc_cli::Result<::std::option::Option<&::std::path::PathBuf>>
		},

		match_and_call! {
			name;
			variants;
			fn is_dev(&self) -> bool
		},

		match_and_call! {
			name;
			variants;
			fn get_roles(&self, is_dev: bool) -> ::sc_cli::Result<::sc_service::Roles>
		},

		match_and_call! {
			name;
			variants;
			fn get_transaction_pool(&self) -> ::sc_cli::Result<::sc_service::config::TransactionPoolOptions>
		},

		{
			let arms = variants
				.iter()
				.map(|x| quote! {
					#name::#x(cmd) => cmd.get_network_config(chain_spec, is_dev, net_config_dir, client_id, node_name, node_key),
				});

			quote! {
				fn get_network_config<G, E>(
					&self,
					chain_spec: &::sc_service::ChainSpec<G, E>,
					is_dev: bool,
					net_config_dir: &::std::path::PathBuf,
					client_id: &str,
					node_name: &str,
					node_key: ::sc_service::config::NodeKeyConfig,
				) -> ::sc_cli::Result<::sc_service::config::NetworkConfiguration>
				where
					G: ::sc_service::RuntimeGenesis,
					E: ::sc_service::ChainSpecExtension,
				{
					match self {
						#( #arms )*
					}
				}
			}
		},

		match_and_call! {
			name;
			variants;
			fn get_keystore_config(&self, base_path: &::std::path::PathBuf) -> ::sc_cli::Result<::sc_service::config::KeystoreConfig>
		},

		match_and_call! {
			name;
			variants;
			fn get_database_cache_size(&self) -> ::sc_cli::Result<::std::option::Option<usize>>
		},

		match_and_call! {
			name;
			variants;
			fn get_database_config(&self, base_path: &::std::path::PathBuf, cache_size: ::std::option::Option<usize>) -> ::sc_cli::Result<::sc_service::config::DatabaseConfig>
		},

		match_and_call! {
			name;
			variants;
			fn get_state_cache_size(&self) -> ::sc_cli::Result<usize>
		},

		match_and_call! {
			name;
			variants;
			fn get_state_cache_child_ratio(&self) -> ::sc_cli::Result<::std::option::Option<usize>>
		},

		match_and_call! {
			name;
			variants;
			fn get_pruning(&self, is_dev: bool, _roles: ::sc_service::Roles) -> ::sc_cli::Result<::sc_service::PruningMode>
		},

		match_and_call! {
			name;
			variants;
			fn get_chain_spec<C: ::sc_cli::SubstrateCLI<G, E>, G, E>(&self) -> ::sc_cli::Result<::sc_service::ChainSpec<G, E>>
			where
				G: ::sc_service::RuntimeGenesis,
				E: ::sc_service::ChainSpecExtension,
		},

		match_and_call! {
			name;
			variants;
			fn get_node_name(&self) -> ::sc_cli::Result<String>
		},

		match_and_call! {
			name;
			variants;
			fn get_wasm_method(&self) -> ::sc_cli::Result<::sc_service::config::WasmExecutionMethod>
		},

		match_and_call! {
			name;
			variants;
			fn get_execution_strategies(&self, is_dev: bool) -> ::sc_cli::Result<::sc_service::config::ExecutionStrategies>
		},

		match_and_call! {
			name;
			variants;
			fn get_rpc_http(&self) -> ::sc_cli::Result<::std::option::Option<::std::net::SocketAddr>>
		},

		match_and_call! {
			name;
			variants;
			fn get_rpc_ws(&self) -> ::sc_cli::Result<::std::option::Option<::std::net::SocketAddr>>
		},

		match_and_call! {
			name;
			variants;
			fn get_rpc_ws_max_connections(&self) -> ::sc_cli::Result<::std::option::Option<usize>>
		},

		match_and_call! {
			name;
			variants;
			fn get_rpc_cors(&self, is_dev: bool) -> ::sc_cli::Result<::std::option::Option<Vec<String>>>
		},

		match_and_call! {
			name;
			variants;
			fn get_prometheus_port(&self) -> ::sc_cli::Result<::std::option::Option<::std::net::SocketAddr>>
		},

		{
			let arms = variants
				.iter()
				.map(|x| quote! {
					#name::#x(cmd) => cmd.get_telemetry_endpoints(chain_spec),
				});

			quote! {
				fn get_telemetry_endpoints<G, E>(
					&self,
					chain_spec: &::sc_service::ChainSpec<G, E>,
				) -> ::sc_cli::Result<::std::option::Option<::sc_service::config::TelemetryEndpoints>> {
					match self {
						#( #arms )*
					}
				}
			}
		},

		match_and_call! {
			name;
			variants;
			fn get_telemetry_external_transport(&self) -> ::sc_cli::Result<::std::option::Option<::sc_service::config::ExtTransport>>
		},

		match_and_call! {
			name;
			variants;
			fn get_default_heap_pages(&self) -> ::sc_cli::Result<::std::option::Option<u64>>
		},

		match_and_call! {
			name;
			variants;
			fn get_offchain_worker(&self, roles: ::sc_service::Roles) -> ::sc_cli::Result<bool>
		},

		match_and_call! {
			name;
			variants;
			fn get_sentry_mode(&self) -> ::sc_cli::Result<bool>
		},

		match_and_call! {
			name;
			variants;
			fn get_force_authoring(&self) -> ::sc_cli::Result<bool>
		},

		match_and_call! {
			name;
			variants;
			fn get_disable_grandpa(&self) -> ::sc_cli::Result<bool>
		},

		match_and_call! {
			name;
			variants;
			fn get_dev_key_seed(&self, is_dev: bool) -> ::sc_cli::Result<::std::option::Option<String>>
		},

		match_and_call! {
			name;
			variants;
			fn get_tracing_targets(&self) -> ::sc_cli::Result<::std::option::Option<String>>
		},

		match_and_call! {
			name;
			variants;
			fn get_tracing_receiver(&self) -> ::sc_cli::Result<::sc_service::TracingReceiver>
		},

		match_and_call! {
			name;
			variants;
			fn get_node_key(&self, net_config_dir: &::std::path::PathBuf) -> ::sc_cli::Result<::sc_service::config::NodeKeyConfig>
		},

		match_and_call! {
			name;
			variants;
			fn create_configuration<C: ::sc_cli::SubstrateCLI<G, E>, G, E>(
				&self,
				task_executor: ::std::sync::Arc<dyn Fn(::std::pin::Pin<Box<dyn ::std::future::Future<Output = ()> + Send>>) + Send + Sync>,
			) -> ::sc_cli::Result<::sc_service::Configuration<G, E>>
			where
				G: ::sc_service::RuntimeGenesis,
				E: ::sc_service::ChainSpecExtension,
		},

		match_and_call! {
			name;
			variants;
			fn init<C: ::sc_cli::SubstrateCLI<G, E>, G, E>(&self) -> ::sc_cli::Result<()>
			where
				G: ::sc_service::RuntimeGenesis,
				E: ::sc_service::ChainSpecExtension,
		},

	];

	quote! {
		impl ::sc_cli::CliConfiguration for #name {
			#( #methods )*
		}
	}
}
