// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Contains the root [`BenchmarkCmd`] command and exports its sub-commands.

mod block;
mod extrinsic;
mod machine;
mod overhead;
mod pallet;
mod shared;
mod storage;

pub use block::BlockCmd;
pub use extrinsic::{ExtrinsicBuilder, ExtrinsicCmd, ExtrinsicFactory};
pub use machine::{MachineCmd, Requirements, SUBSTRATE_REFERENCE_HARDWARE};
pub use overhead::OverheadCmd;
pub use pallet::PalletCmd;
pub use sc_service::BasePath;
pub use storage::StorageCmd;

use sc_cli::{CliConfiguration, DatabaseParams, ImportParams, PruningParams, Result, SharedParams};

/// The root `benchmarking` command.
///
/// Has no effect itself besides printing a help menu of the sub-commands.
#[derive(Debug, clap::Subcommand)]
pub enum BenchmarkCmd {
	Pallet(PalletCmd),
	Storage(StorageCmd),
	Overhead(OverheadCmd),
	Block(BlockCmd),
	Machine(MachineCmd),
	Extrinsic(ExtrinsicCmd),
}

/// Unwraps a [`BenchmarkCmd`] into its concrete sub-command.
macro_rules! unwrap_cmd {
	{
		$self:expr,
		$cmd:ident,
		$code:expr
	} => {
		match $self {
			BenchmarkCmd::Pallet($cmd) => $code,
			BenchmarkCmd::Storage($cmd) => $code,
			BenchmarkCmd::Overhead($cmd) => $code,
			BenchmarkCmd::Block($cmd) => $code,
			BenchmarkCmd::Machine($cmd) => $code,
			BenchmarkCmd::Extrinsic($cmd) => $code,
		}
	}
}

/// Forward the [`CliConfiguration`] trait implementation.
///
/// Each time a sub-command exposes a new config option, it must be added here.
impl CliConfiguration for BenchmarkCmd {
	fn shared_params(&self) -> &SharedParams {
		unwrap_cmd! {
			self, cmd, cmd.shared_params()
		}
	}

	fn import_params(&self) -> Option<&ImportParams> {
		unwrap_cmd! {
			self, cmd, cmd.import_params()
		}
	}

	fn database_params(&self) -> Option<&DatabaseParams> {
		unwrap_cmd! {
			self, cmd, cmd.database_params()
		}
	}

	fn base_path(&self) -> Result<Option<BasePath>> {
		let inner = unwrap_cmd! {
			self, cmd, cmd.base_path()
		};

		// If the base path was not provided, benchmark command shall use temporary path. Otherwise
		// we may end up using shared path, which may be inappropriate for benchmarking.
		match inner {
			Ok(None) => Some(BasePath::new_temp_dir()).transpose().map_err(|e| e.into()),
			e => e,
		}
	}

	fn pruning_params(&self) -> Option<&PruningParams> {
		unwrap_cmd! {
			self, cmd, cmd.pruning_params()
		}
	}

	fn trie_cache_maximum_size(&self) -> Result<Option<usize>> {
		unwrap_cmd! {
			self, cmd, cmd.trie_cache_maximum_size()
		}
	}

	fn chain_id(&self, is_dev: bool) -> Result<String> {
		unwrap_cmd! {
			self, cmd, cmd.chain_id(is_dev)
		}
	}
}
