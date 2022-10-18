// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

//! Offchain worker related configuration parameters.
//!
//! A subset of configuration parameters which are relevant to
//! the inner working of offchain workers. The usage is solely
//! targeted at handling input parameter parsing providing
//! a reasonable abstraction.

use clap::Args;
use sc_network::config::Role;
use sc_service::config::OffchainWorkerConfig;

use crate::{error, OffchainWorkerEnabled};

/// Offchain worker related parameters.
#[derive(Debug, Clone, Args)]
pub struct OffchainWorkerParams {
	/// Should execute offchain workers on every block.
	///
	/// By default it's only enabled for nodes that are authoring new blocks.
	#[arg(
		long = "offchain-worker",
		value_name = "ENABLED",
		value_enum,
		ignore_case = true,
		default_value_t = OffchainWorkerEnabled::WhenValidating
	)]
	pub enabled: OffchainWorkerEnabled,

	/// Enable Offchain Indexing API, which allows block import to write to Offchain DB.
	///
	/// Enables a runtime to write directly to a offchain workers
	/// DB during block import.
	#[arg(long = "enable-offchain-indexing", value_name = "ENABLE_OFFCHAIN_INDEXING")]
	pub indexing_enabled: bool,
}

impl OffchainWorkerParams {
	/// Load spec to `Configuration` from `OffchainWorkerParams` and spec factory.
	pub fn offchain_worker(&self, role: &Role) -> error::Result<OffchainWorkerConfig> {
		let enabled = match (&self.enabled, role) {
			(OffchainWorkerEnabled::WhenValidating, Role::Authority { .. }) => true,
			(OffchainWorkerEnabled::Always, _) => true,
			(OffchainWorkerEnabled::Never, _) => false,
			(OffchainWorkerEnabled::WhenValidating, _) => false,
		};

		let indexing_enabled = self.indexing_enabled;
		Ok(OffchainWorkerConfig { enabled, indexing_enabled })
	}
}
