// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

mod build_spec_cmd;
mod check_block_cmd;
mod export_blocks_cmd;
mod export_state_cmd;
mod import_blocks_cmd;
mod purge_chain_cmd;
mod revert_cmd;
mod run_cmd;

pub use self::build_spec_cmd::BuildSpecCmd;
pub use self::check_block_cmd::CheckBlockCmd;
pub use self::export_blocks_cmd::ExportBlocksCmd;
pub use self::import_blocks_cmd::ImportBlocksCmd;
pub use self::purge_chain_cmd::PurgeChainCmd;
pub use self::revert_cmd::RevertCmd;
pub use self::run_cmd::RunCmd;
pub use self::export_state_cmd::ExportStateCmd;
use std::fmt::Debug;
use structopt::StructOpt;

/// All core commands that are provided by default.
///
/// The core commands are split into multiple subcommands and `Run` is the default subcommand. From
/// the CLI user perspective, it is not visible that `Run` is a subcommand. So, all parameters of
/// `Run` are exported as main executable parameters.
#[derive(Debug, Clone, StructOpt)]
pub enum Subcommand {
	/// Build a spec.json file, outputs to stdout.
	BuildSpec(BuildSpecCmd),

	/// Export blocks to a file.
	ExportBlocks(ExportBlocksCmd),

	/// Import blocks from file.
	ImportBlocks(ImportBlocksCmd),

	/// Validate a single block.
	CheckBlock(CheckBlockCmd),

	/// Revert chain to the previous state.
	Revert(RevertCmd),

	/// Remove the whole chain data.
	PurgeChain(PurgeChainCmd),

	/// Export state as raw chain spec.
	ExportState(ExportStateCmd),
}

// TODO: move to config.rs?
/// Macro that helps implement CliConfiguration on an enum of subcommand automatically
///
/// # Example
///
/// ```
/// # #[macro_use] extern crate sc_cli;
///
/// # struct EmptyVariant {}
///
///	# impl sc_cli::CliConfiguration for EmptyVariant {
///	#     fn shared_params(&self) -> &sc_cli::SharedParams { unimplemented!() }
///	#     fn chain_id(&self, _: bool) -> sc_cli::Result<String> { Ok("test-chain-id".to_string()) }
///	# }
///
/// # fn main() {
/// enum Subcommand {
///	    Variant1(EmptyVariant),
///	    Variant2(EmptyVariant),
///	}
///
/// substrate_cli_subcommands!(
///     Subcommand => Variant1, Variant2
/// );
///
/// # use sc_cli::CliConfiguration;
/// # assert_eq!(Subcommand::Variant1(EmptyVariant {}).chain_id(false).unwrap(), "test-chain-id");
///
/// # }
/// ```
///
/// Which will expand to:
///
/// ```ignore
/// impl CliConfiguration for Subcommand {
///	    fn base_path(&self) -> Result<Option<PathBuf>> {
///	        match self {
///	            Subcommand::Variant1(cmd) => cmd.base_path(),
///	            Subcommand::Variant2(cmd) => cmd.base_path(),
///	        }
///	    }
///
///	    fn is_dev(&self) -> Result<bool> {
///	        match self {
///	            Subcommand::Variant1(cmd) => cmd.is_dev(),
///	            Subcommand::Variant2(cmd) => cmd.is_dev(),
///	        }
///	    }
///
///     // ...
/// }
/// ```
#[macro_export]
macro_rules! substrate_cli_subcommands {
	($enum:ident => $($variant:ident),*) => {
		impl $crate::CliConfiguration for $enum {
			fn shared_params(&self) -> &$crate::SharedParams {
				match self {
					$($enum::$variant(cmd) => cmd.shared_params()),*
				}
			}

			fn import_params(&self) -> Option<&$crate::ImportParams> {
				match self {
					$($enum::$variant(cmd) => cmd.import_params()),*
				}
			}

			fn pruning_params(&self) -> Option<&$crate::PruningParams> {
				match self {
					$($enum::$variant(cmd) => cmd.pruning_params()),*
				}
			}

			fn keystore_params(&self) -> Option<&$crate::KeystoreParams> {
				match self {
					$($enum::$variant(cmd) => cmd.keystore_params()),*
				}
			}

			fn network_params(&self) -> Option<&$crate::NetworkParams> {
				match self {
					$($enum::$variant(cmd) => cmd.network_params()),*
				}
			}

			fn offchain_worker_params(&self) -> Option<&$crate::OffchainWorkerParams> {
				match self {
					$($enum::$variant(cmd) => cmd.offchain_worker_params()),*
				}
			}

			fn database_params(&self) -> Option<&$crate::DatabaseParams> {
				match self {
					$($enum::$variant(cmd) => cmd.database_params()),*
				}
			}

			fn base_path(&self) -> $crate::Result<::std::option::Option<::std::path::PathBuf>> {
				match self {
					$($enum::$variant(cmd) => cmd.base_path()),*
				}
			}

			fn is_dev(&self) -> $crate::Result<bool> {
				match self {
					$($enum::$variant(cmd) => cmd.is_dev()),*
				}
			}

			fn role(&self, is_dev: bool) -> $crate::Result<::sc_service::Role> {
				match self {
					$($enum::$variant(cmd) => cmd.role(is_dev)),*
				}
			}

			fn transaction_pool(&self)
			-> $crate::Result<::sc_service::config::TransactionPoolOptions> {
				match self {
					$($enum::$variant(cmd) => cmd.transaction_pool()),*
				}
			}

			fn network_config(
				&self,
				chain_spec: &::std::boxed::Box<dyn ::sc_service::ChainSpec>,
				is_dev: bool,
				net_config_dir: ::std::path::PathBuf,
				client_id: &str,
				node_name: &str,
				node_key: ::sc_service::config::NodeKeyConfig,
			) -> $crate::Result<::sc_service::config::NetworkConfiguration> {
				match self {
					$(
						$enum::$variant(cmd) => cmd.network_config(
							chain_spec, is_dev, net_config_dir, client_id, node_name, node_key
						)
					),*
				}
			}

			fn keystore_config(&self, base_path: &::std::path::PathBuf)
			-> $crate::Result<::sc_service::config::KeystoreConfig> {
				match self {
					$($enum::$variant(cmd) => cmd.keystore_config(base_path)),*
				}
			}

			fn database_cache_size(&self) -> $crate::Result<::std::option::Option<usize>> {
				match self {
					$($enum::$variant(cmd) => cmd.database_cache_size()),*
				}
			}

			fn database_config(
				&self,
				base_path: &::std::path::PathBuf,
				cache_size: usize,
				database: $crate::Database,
			) -> $crate::Result<::sc_service::config::DatabaseConfig> {
				match self {
					$($enum::$variant(cmd) => cmd.database_config(base_path, cache_size, database)),*
				}
			}

			fn database(&self) -> $crate::Result<::std::option::Option<$crate::Database>> {
				match self {
					$($enum::$variant(cmd) => cmd.database()),*
				}
			}

			fn state_cache_size(&self) -> $crate::Result<usize> {
				match self {
					$($enum::$variant(cmd) => cmd.state_cache_size()),*
				}
			}

			fn state_cache_child_ratio(&self) -> $crate::Result<::std::option::Option<usize>> {
				match self {
					$($enum::$variant(cmd) => cmd.state_cache_child_ratio()),*
				}
			}

			fn pruning(&self, unsafe_pruning: bool, role: &::sc_service::Role)
			-> $crate::Result<::sc_service::config::PruningMode> {
				match self {
					$($enum::$variant(cmd) => cmd.pruning(unsafe_pruning, role)),*
				}
			}

			fn chain_id(&self, is_dev: bool) -> $crate::Result<String> {
				match self {
					$($enum::$variant(cmd) => cmd.chain_id(is_dev)),*
				}
			}

			fn init<C: $crate::SubstrateCli>(&self) -> $crate::Result<()> {
				match self {
					$($enum::$variant(cmd) => cmd.init::<C>()),*
				}
			}

			fn node_name(&self) -> $crate::Result<String> {
				match self {
					$($enum::$variant(cmd) => cmd.node_name()),*
				}
			}

			fn wasm_method(&self) -> $crate::Result<::sc_service::config::WasmExecutionMethod> {
				match self {
					$($enum::$variant(cmd) => cmd.wasm_method()),*
				}
			}

			fn execution_strategies(&self, is_dev: bool)
			-> $crate::Result<::sc_client_api::execution_extensions::ExecutionStrategies> {
				match self {
					$($enum::$variant(cmd) => cmd.execution_strategies(is_dev)),*
				}
			}

			fn rpc_http(&self) -> $crate::Result<::std::option::Option<::std::net::SocketAddr>> {
				match self {
					$($enum::$variant(cmd) => cmd.rpc_http()),*
				}
			}

			fn rpc_ws(&self) -> $crate::Result<::std::option::Option<::std::net::SocketAddr>> {
				match self {
					$($enum::$variant(cmd) => cmd.rpc_ws()),*
				}
			}

			fn rpc_methods(&self) -> $crate::Result<sc_service::config::RpcMethods> {
				match self {
					$($enum::$variant(cmd) => cmd.rpc_methods()),*
				}
			}

			fn rpc_ws_max_connections(&self) -> $crate::Result<::std::option::Option<usize>> {
				match self {
					$($enum::$variant(cmd) => cmd.rpc_ws_max_connections()),*
				}
			}

			fn rpc_cors(&self, is_dev: bool)
			-> $crate::Result<::std::option::Option<::std::vec::Vec<String>>> {
				match self {
					$($enum::$variant(cmd) => cmd.rpc_cors(is_dev)),*
				}
			}

			fn prometheus_config(&self)
			-> $crate::Result<::std::option::Option<::sc_service::config::PrometheusConfig>> {
				match self {
					$($enum::$variant(cmd) => cmd.prometheus_config()),*
				}
			}

			fn telemetry_endpoints(
				&self,
				chain_spec: &Box<dyn ::sc_service::ChainSpec>,
			) -> $crate::Result<::std::option::Option<::sc_service::config::TelemetryEndpoints>> {
				match self {
					$($enum::$variant(cmd) => cmd.telemetry_endpoints(chain_spec)),*
				}
			}

			fn telemetry_external_transport(&self)
			-> $crate::Result<::std::option::Option<::sc_service::config::ExtTransport>> {
				match self {
					$($enum::$variant(cmd) => cmd.telemetry_external_transport()),*
				}
			}

			fn default_heap_pages(&self) -> $crate::Result<::std::option::Option<u64>> {
				match self {
					$($enum::$variant(cmd) => cmd.default_heap_pages()),*
				}
			}

			fn offchain_worker(
				&self,
				role: &::sc_service::Role,
			) -> $crate::Result<::sc_service::config::OffchainWorkerConfig> {
				match self {
					$($enum::$variant(cmd) => cmd.offchain_worker(role)),*
				}
			}

			fn force_authoring(&self) -> $crate::Result<bool> {
				match self {
					$($enum::$variant(cmd) => cmd.force_authoring()),*
				}
			}

			fn disable_grandpa(&self) -> $crate::Result<bool> {
				match self {
					$($enum::$variant(cmd) => cmd.disable_grandpa()),*
				}
			}

			fn dev_key_seed(&self, is_dev: bool) -> $crate::Result<::std::option::Option<String>> {
				match self {
					$($enum::$variant(cmd) => cmd.dev_key_seed(is_dev)),*
				}
			}

			fn tracing_targets(&self) -> $crate::Result<::std::option::Option<String>> {
				match self {
					$($enum::$variant(cmd) => cmd.tracing_targets()),*
				}
			}

			fn tracing_receiver(&self) -> $crate::Result<::sc_service::TracingReceiver> {
				match self {
					$($enum::$variant(cmd) => cmd.tracing_receiver()),*
				}
			}

			fn node_key(&self, net_config_dir: &::std::path::PathBuf)
			-> $crate::Result<::sc_service::config::NodeKeyConfig> {
				match self {
					$($enum::$variant(cmd) => cmd.node_key(net_config_dir)),*
				}
			}

			fn max_runtime_instances(&self) -> $crate::Result<::std::option::Option<usize>> {
				match self {
					$($enum::$variant(cmd) => cmd.max_runtime_instances()),*
				}
			}

			fn log_filters(&self) -> $crate::Result<String> {
				match self {
					$($enum::$variant(cmd) => cmd.log_filters()),*
				}
			}
		}
	}
}

substrate_cli_subcommands!(
	Subcommand => BuildSpec, ExportBlocks, ImportBlocks, CheckBlock, Revert, PurgeChain, ExportState
);

