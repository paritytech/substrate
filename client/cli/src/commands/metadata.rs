// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

//! Metadata related CLI utilities

use super::MetadataDump;
use crate::{CliConfiguration, Error, SharedParams};
use sc_client_api::UsageProvider;
use sc_service::Arc;
use sp_api::{Metadata, ProvideRuntimeApi};
use sp_runtime::traits::Block as BlockT;
use structopt::StructOpt;

/// Cli subcommand for interacting with the runtime metadata.
#[derive(Debug, StructOpt)]
pub enum MetadataSubcommand {
	/// Dump the runtime to a file or to stdout.
	Dump(MetadataDump),
}

impl MetadataSubcommand {
	/// run the metadata subcommands
	pub fn run<B, C>(&self, client: Arc<C>) -> Result<(), Error>
	where
		B: BlockT,
		C: ProvideRuntimeApi<B> + UsageProvider<B>,
		C::Api: Metadata<B>,
	{
		match self {
			Self::Dump(cmd) => cmd.run(client),
		}
	}
}

impl CliConfiguration for MetadataSubcommand {
	fn shared_params(&self) -> &SharedParams {
		match self {
			Self::Dump(cmd) => cmd.shared_params(),
		}
	}

	fn base_path(&self) -> crate::Result<Option<sc_service::BasePath>> {
		match self {
			Self::Dump(cmd) => cmd.base_path(),
		}
	}
}
