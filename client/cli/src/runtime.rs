// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

use std::fmt::Debug;
use std::marker::PhantomData;
use std::sync::Arc;

use futures::{Future, future, future::FutureExt};
use futures::select;
use futures::pin_mut;
use sc_service::{
	AbstractService, Configuration, RuntimeGenesis, ChainSpecExtension,
	ServiceBuilderCommand,
};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};
use crate::error;
use crate::SubstrateCLI;
use crate::CliConfiguration;
use crate::{RunCmd, Subcommand};

#[cfg(target_family = "unix")]
async fn main<F, E>(func: F) -> Result<(), Box<dyn std::error::Error>>
where
	F: Future<Output = Result<(), E>> + future::FusedFuture,
	E: 'static + std::error::Error,
{
	use tokio::signal::unix::{signal, SignalKind};

	let mut stream_int = signal(SignalKind::interrupt())?;
	let mut stream_term = signal(SignalKind::terminate())?;

	let t1 = stream_int.recv().fuse();
	let t2 = stream_term.recv().fuse();
	let t3 = func;

	pin_mut!(t1, t2, t3);

	select! {
		_ = t1 => {},
		_ = t2 => {},
		res = t3 => res?,
	}

	Ok(())
}

#[cfg(not(unix))]
async fn main<F, E>(func: F) -> Result<(), Box<dyn std::error::Error>>
where
	F: Future<Output = Result<(), E>> + future::FusedFuture,
	E: 'static + std::error::Error,
{
	use tokio::signal::ctrl_c;

	let t1 = ctrl_c().fuse();
	let t2 = func;

	pin_mut!(t1, t2);

	select! {
		_ = t1 => {},
		res = t2 => res?,
	}

	Ok(())
}

fn build_runtime() -> Result<tokio::runtime::Runtime, std::io::Error> {
	tokio::runtime::Builder::new()
		.thread_name("main-tokio-")
		.threaded_scheduler()
		.enable_all()
		.build()
}

/// A helper function that runs a future with tokio and stops if the process receives the signal
/// SIGTERM or SIGINT
pub fn run_until_exit<FUT, ERR, G, E, F>(
	mut config: Configuration<G, E>,
	future_builder: F,
) -> error::Result<()>
where
	F: FnOnce(Configuration<G, E>) -> error::Result<FUT>,
	FUT: Future<Output = Result<(), ERR>> + future::Future,
	ERR: 'static + std::error::Error,
{
	let mut runtime = build_runtime()?;

	config.task_executor = {
		let runtime_handle = runtime.handle().clone();
		Arc::new(move |fut| { runtime_handle.spawn(fut); })
	};

	let f = future_builder(config)?;
	let f = f.fuse();
	pin_mut!(f);

	runtime.block_on(main(f)).map_err(|e| e.to_string())?;

	Ok(())
}

/// A helper function that runs an `AbstractService` with tokio and stops if the process receives
/// the signal SIGTERM or SIGINT
pub fn run_service_until_exit<T, G, E, F>(
	mut config: Configuration<G, E>,
	service_builder: F,
) -> error::Result<()>
where
	F: FnOnce(Configuration<G, E>) -> Result<T, sc_service::error::Error>,
	T: AbstractService + Unpin,
{
	let mut runtime = build_runtime()?;

	config.task_executor = {
		let runtime_handle = runtime.handle().clone();
		Arc::new(move |fut| { runtime_handle.spawn(fut); })
	};

	let service = service_builder(config)?;

	let informant_future = sc_informant::build(&service, sc_informant::OutputFormat::Coloured);
	let _informant_handle = runtime.spawn(informant_future);

	// we eagerly drop the service so that the internal exit future is fired,
	// but we need to keep holding a reference to the global telemetry guard
	// and drop the runtime first.
	let _telemetry = service.telemetry();

	let f = service.fuse();
	pin_mut!(f);

	runtime.block_on(main(f)).map_err(|e| e.to_string())?;
	drop(runtime);

	Ok(())
}

pub struct Runtime<C: SubstrateCLI<G, E>, G, E>
where
	G: RuntimeGenesis,
	E: ChainSpecExtension,
{
	pub config: Configuration<G, E>,
	pub tokio_runtime: tokio::runtime::Runtime,
	phantom: PhantomData<C>,
}

impl<C: SubstrateCLI<G, E>, G, E> Runtime<C, G, E>
where
	G: RuntimeGenesis,
	E: ChainSpecExtension,
{
	pub fn new<T: CliConfiguration>(cli_config: &T) -> error::Result<Runtime<C, G, E>> {
		let tokio_runtime = build_runtime()?;

		Ok(Runtime {
			config: cli_config.into_configuration::<C, G, E>()?,
			tokio_runtime,
			phantom: PhantomData,
		})
	}

	pub fn run_node<FNL, FNF, SL, SF>(self, new_light: FNL, new_full: FNF) -> error::Result<()>
	where
		FNL: FnOnce(Configuration<G, E>) -> sc_service::error::Result<SL>,
		FNF: FnOnce(Configuration<G, E>) -> sc_service::error::Result<SF>,
		SL: AbstractService + Unpin,
		SF: AbstractService + Unpin,
	{
		RunCmd::run::<C, G, E, FNL, FNF, SL, SF>(self.config, new_light, new_full)
	}

	pub fn run_subcommand<B, BC, BB>(self, subcommand: &Subcommand, builder: B) -> error::Result<()>
	where
		B: FnOnce(Configuration<G, E>) -> sc_service::error::Result<BC>,
		BC: ServiceBuilderCommand<Block = BB> + Unpin,
		BB: sp_runtime::traits::Block + Debug,
		<<<BB as BlockT>::Header as HeaderT>::Number as std::str::FromStr>::Err: Debug,
		<BB as BlockT>::Hash: std::str::FromStr,
	{
		subcommand.run::<G, E, B, BC, BB>(self.config, builder)
	}
}
