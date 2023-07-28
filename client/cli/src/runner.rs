// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use crate::{error::Error as CliError, Result, Signals, SubstrateCli};
use chrono::prelude::*;
use futures::{future::FutureExt, Future};
use log::info;
use sc_service::{Configuration, Error as ServiceError, TaskManager};
use sc_utils::metrics::{TOKIO_THREADS_ALIVE, TOKIO_THREADS_TOTAL};
use std::{marker::PhantomData, time::Duration};

/// Build a tokio runtime with all features.
pub fn build_runtime() -> std::result::Result<tokio::runtime::Runtime, std::io::Error> {
	tokio::runtime::Builder::new_multi_thread()
		.on_thread_start(|| {
			TOKIO_THREADS_ALIVE.inc();
			TOKIO_THREADS_TOTAL.inc();
		})
		.on_thread_stop(|| {
			TOKIO_THREADS_ALIVE.dec();
		})
		.enable_all()
		.build()
}

/// A Substrate CLI runtime that can be used to run a node or a command
pub struct Runner<C: SubstrateCli> {
	config: Configuration,
	tokio_runtime: tokio::runtime::Runtime,
	signals: Signals,
	phantom: PhantomData<C>,
}

impl<C: SubstrateCli> Runner<C> {
	/// Create a new runtime with the command provided in argument
	pub fn new(
		config: Configuration,
		tokio_runtime: tokio::runtime::Runtime,
		signals: Signals,
	) -> Result<Runner<C>> {
		Ok(Runner { config, tokio_runtime, signals, phantom: PhantomData })
	}

	/// Log information about the node itself.
	///
	/// # Example:
	///
	/// ```text
	/// 2020-06-03 16:14:21 Substrate Node
	/// 2020-06-03 16:14:21 ✌️  version 2.0.0-rc3-f4940588c-x86_64-linux-gnu
	/// 2020-06-03 16:14:21 ❤️  by Parity Technologies <admin@parity.io>, 2017-2020
	/// 2020-06-03 16:14:21 📋 Chain specification: Flaming Fir
	/// 2020-06-03 16:14:21 🏷  Node name: jolly-rod-7462
	/// 2020-06-03 16:14:21 👤 Role: FULL
	/// 2020-06-03 16:14:21 💾 Database: RocksDb at /tmp/c/chains/flamingfir7/db
	/// 2020-06-03 16:14:21 ⛓  Native runtime: node-251 (substrate-node-1.tx1.au10)
	/// ```
	fn print_node_infos(&self) {
		print_node_infos::<C>(self.config())
	}

	/// A helper function that runs a node with tokio and stops if the process receives the signal
	/// `SIGTERM` or `SIGINT`.
	pub fn run_node_until_exit<F, E>(
		self,
		initialize: impl FnOnce(Configuration) -> F,
	) -> std::result::Result<(), E>
	where
		F: Future<Output = std::result::Result<TaskManager, E>>,
		E: std::error::Error + Send + Sync + 'static + From<ServiceError>,
	{
		self.print_node_infos();

		let mut task_manager = self.tokio_runtime.block_on(initialize(self.config))?;

		let res = self
			.tokio_runtime
			.block_on(self.signals.run_until_signal(task_manager.future().fuse()));
		// We need to drop the task manager here to inform all tasks that they should shut down.
		//
		// This is important to be done before we instruct the tokio runtime to shutdown. Otherwise
		// the tokio runtime will wait the full 60 seconds for all tasks to stop.
		let task_registry = task_manager.into_task_registry();

		// Give all futures 60 seconds to shutdown, before tokio "leaks" them.
		let shutdown_timeout = Duration::from_secs(60);
		self.tokio_runtime.shutdown_timeout(shutdown_timeout);

		let running_tasks = task_registry.running_tasks();

		if !running_tasks.is_empty() {
			log::error!("Detected running(potentially stalled) tasks on shutdown:");
			running_tasks.iter().for_each(|(task, count)| {
				let instances_desc =
					if *count > 1 { format!("with {} instances ", count) } else { "".to_string() };

				if task.is_default_group() {
					log::error!(
						"Task \"{}\" was still running {}after waiting {} seconds to finish.",
						task.name,
						instances_desc,
						shutdown_timeout.as_secs(),
					);
				} else {
					log::error!(
						"Task \"{}\" (Group: {}) was still running {}after waiting {} seconds to finish.",
						task.name,
						task.group,
						instances_desc,
						shutdown_timeout.as_secs(),
					);
				}
			});
		}

		res.map_err(Into::into)
	}

	/// A helper function that runs a command with the configuration of this node.
	pub fn sync_run<E>(
		self,
		runner: impl FnOnce(Configuration) -> std::result::Result<(), E>,
	) -> std::result::Result<(), E>
	where
		E: std::error::Error + Send + Sync + 'static + From<ServiceError>,
	{
		runner(self.config)
	}

	/// A helper function that runs a future with tokio and stops if the process receives
	/// the signal `SIGTERM` or `SIGINT`.
	pub fn async_run<F, E>(
		self,
		runner: impl FnOnce(Configuration) -> std::result::Result<(F, TaskManager), E>,
	) -> std::result::Result<(), E>
	where
		F: Future<Output = std::result::Result<(), E>>,
		E: std::error::Error + Send + Sync + 'static + From<ServiceError> + From<CliError>,
	{
		let (future, task_manager) = runner(self.config)?;
		self.tokio_runtime.block_on(self.signals.run_until_signal(future.fuse()))?;
		// Drop the task manager before dropping the rest, to ensure that all futures were informed
		// about the shut down.
		drop(task_manager);
		Ok(())
	}

	/// Get an immutable reference to the node Configuration
	pub fn config(&self) -> &Configuration {
		&self.config
	}

	/// Get a mutable reference to the node Configuration
	pub fn config_mut(&mut self) -> &mut Configuration {
		&mut self.config
	}
}

/// Log information about the node itself.
pub fn print_node_infos<C: SubstrateCli>(config: &Configuration) {
	info!("{}", C::impl_name());
	info!("✌️  version {}", C::impl_version());
	info!("❤️  by {}, {}-{}", C::author(), C::copyright_start_year(), Local::now().year());
	info!("📋 Chain specification: {}", config.chain_spec.name());
	info!("🏷  Node name: {}", config.network.node_name);
	info!("👤 Role: {}", config.display_role());
	info!(
		"💾 Database: {} at {}",
		config.database,
		config
			.database
			.path()
			.map_or_else(|| "<unknown>".to_owned(), |p| p.display().to_string())
	);
}

#[cfg(test)]
mod tests {
	use super::*;
	use sc_network::config::NetworkConfiguration;
	use sc_service::{Arc, ChainType, GenericChainSpec, NoExtension};
	use std::{
		path::PathBuf,
		sync::atomic::{AtomicU64, Ordering},
	};

	struct Cli;

	impl SubstrateCli for Cli {
		fn author() -> String {
			"test".into()
		}

		fn impl_name() -> String {
			"yep".into()
		}

		fn impl_version() -> String {
			"version".into()
		}

		fn description() -> String {
			"desc".into()
		}

		fn support_url() -> String {
			"no.pe".into()
		}

		fn copyright_start_year() -> i32 {
			2042
		}

		fn load_spec(
			&self,
			_: &str,
		) -> std::result::Result<Box<dyn sc_service::ChainSpec>, String> {
			Err("nope".into())
		}
	}

	fn create_runner() -> Runner<Cli> {
		let runtime = build_runtime().unwrap();

		let root = PathBuf::from("db");
		let runner = Runner::new(
			Configuration {
				impl_name: "spec".into(),
				impl_version: "3".into(),
				role: sc_service::Role::Authority,
				tokio_handle: runtime.handle().clone(),
				transaction_pool: Default::default(),
				network: NetworkConfiguration::new_memory(),
				keystore: sc_service::config::KeystoreConfig::InMemory,
				database: sc_client_db::DatabaseSource::ParityDb { path: root.clone() },
				trie_cache_maximum_size: None,
				state_pruning: None,
				blocks_pruning: sc_client_db::BlocksPruning::KeepAll,
				chain_spec: Box::new(GenericChainSpec::from_genesis(
					"test",
					"test_id",
					ChainType::Development,
					|| unimplemented!("Not required in tests"),
					Vec::new(),
					None,
					None,
					None,
					None,
					NoExtension::None,
				)),
				wasm_method: Default::default(),
				wasm_runtime_overrides: None,
				rpc_addr: None,
				rpc_max_connections: Default::default(),
				rpc_cors: None,
				rpc_methods: Default::default(),
				rpc_max_request_size: Default::default(),
				rpc_max_response_size: Default::default(),
				rpc_id_provider: Default::default(),
				rpc_max_subs_per_conn: Default::default(),
				rpc_port: 9944,
				prometheus_config: None,
				telemetry_endpoints: None,
				default_heap_pages: None,
				offchain_worker: Default::default(),
				force_authoring: false,
				disable_grandpa: false,
				dev_key_seed: None,
				tracing_targets: None,
				tracing_receiver: Default::default(),
				max_runtime_instances: 8,
				announce_block: true,
				base_path: sc_service::BasePath::new(root.clone()),
				data_path: root,
				informant_output_format: Default::default(),
				runtime_cache_size: 2,
			},
			runtime,
			Signals::dummy(),
		)
		.unwrap();

		runner
	}

	#[test]
	fn ensure_run_until_exit_informs_tasks_to_end() {
		let runner = create_runner();

		let counter = Arc::new(AtomicU64::new(0));
		let counter2 = counter.clone();

		runner
			.run_node_until_exit(move |cfg| async move {
				let task_manager = TaskManager::new(cfg.tokio_handle.clone(), None).unwrap();
				let (sender, receiver) = futures::channel::oneshot::channel();

				// We need to use `spawn_blocking` here so that we get a dedicated thread for our
				// future. This is important for this test, as otherwise tokio can just "drop" the
				// future.
				task_manager.spawn_handle().spawn_blocking("test", None, async move {
					let _ = sender.send(());
					loop {
						counter2.fetch_add(1, Ordering::Relaxed);
						futures_timer::Delay::new(Duration::from_millis(50)).await;
					}
				});

				task_manager.spawn_essential_handle().spawn_blocking("test2", None, async {
					// Let's stop this essential task directly when our other task started.
					// It will signal that the task manager should end.
					let _ = receiver.await;
				});

				Ok::<_, sc_service::Error>(task_manager)
			})
			.unwrap_err();

		let count = counter.load(Ordering::Relaxed);

		// Ensure that our counting task was running for less than 30 seconds.
		// It should be directly killed, but for CI and whatever we are being a little bit more
		// "relaxed".
		assert!((count as u128) < (Duration::from_secs(30).as_millis() / 50));
	}

	fn run_test_in_another_process(
		test_name: &str,
		test_body: impl FnOnce(),
	) -> Option<std::process::Output> {
		if std::env::var("RUN_FORKED_TEST").is_ok() {
			test_body();
			None
		} else {
			let output = std::process::Command::new(std::env::current_exe().unwrap())
				.arg(test_name)
				.env("RUN_FORKED_TEST", "1")
				.output()
				.unwrap();

			assert!(output.status.success());
			Some(output)
		}
	}

	/// This test ensures that `run_node_until_exit` aborts waiting for "stuck" tasks after 60
	/// seconds, aka doesn't wait until they are finished (which may never happen).
	#[test]
	fn ensure_run_until_exit_is_not_blocking_indefinitely() {
		let output = run_test_in_another_process(
			"ensure_run_until_exit_is_not_blocking_indefinitely",
			|| {
				sp_tracing::try_init_simple();

				let runner = create_runner();

				runner
					.run_node_until_exit(move |cfg| async move {
						let task_manager =
							TaskManager::new(cfg.tokio_handle.clone(), None).unwrap();
						let (sender, receiver) = futures::channel::oneshot::channel();

						// We need to use `spawn_blocking` here so that we get a dedicated thread
						// for our future. This future is more blocking code that will never end.
						task_manager.spawn_handle().spawn_blocking("test", None, async move {
							let _ = sender.send(());
							loop {
								std::thread::sleep(Duration::from_secs(30));
							}
						});

						task_manager.spawn_essential_handle().spawn_blocking(
							"test2",
							None,
							async {
								// Let's stop this essential task directly when our other task
								// started. It will signal that the task manager should end.
								let _ = receiver.await;
							},
						);

						Ok::<_, sc_service::Error>(task_manager)
					})
					.unwrap_err();
			},
		);

		let Some(output) = output else { return };

		let stderr = dbg!(String::from_utf8(output.stderr).unwrap());

		assert!(
			stderr.contains("Task \"test\" was still running after waiting 60 seconds to finish.")
		);
		assert!(!stderr
			.contains("Task \"test2\" was still running after waiting 60 seconds to finish."));
	}
}
