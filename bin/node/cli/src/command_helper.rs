// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Contains code to setup the command invocations in [`super::command`] which would
//! otherwise bloat that module.

use crate::service::{create_extrinsic, FullClient};

use node_runtime::SystemCall;
use sc_cli::Result;
use sp_inherents::{InherentData, InherentDataProvider};
use sp_keyring::Sr25519Keyring;
use sp_runtime::OpaqueExtrinsic;

use std::{sync::Arc, time::Duration};

/// Generates extrinsics for the `benchmark overhead` command.
pub struct BenchmarkExtrinsicBuilder {
	client: Arc<FullClient>,
}

impl BenchmarkExtrinsicBuilder {
	/// Creates a new [`Self`] from the given client.
	pub fn new(client: Arc<FullClient>) -> Self {
		Self { client }
	}
}

impl frame_benchmarking_cli::ExtrinsicBuilder for BenchmarkExtrinsicBuilder {
	fn remark(&self, nonce: u32) -> std::result::Result<OpaqueExtrinsic, &'static str> {
		let acc = Sr25519Keyring::Bob.pair();
		let extrinsic: OpaqueExtrinsic = create_extrinsic(
			self.client.as_ref(),
			acc,
			SystemCall::remark { remark: vec![] },
			Some(nonce),
		)
		.into();

		Ok(extrinsic)
	}
}

/// Generates inherent data for the `benchmark overhead` command.
pub fn inherent_benchmark_data() -> Result<InherentData> {
	let mut inherent_data = InherentData::new();
	let d = Duration::from_millis(0);
	let timestamp = sp_timestamp::InherentDataProvider::new(d.into());

	timestamp
		.provide_inherent_data(&mut inherent_data)
		.map_err(|e| format!("creating inherent data: {:?}", e))?;
	Ok(inherent_data)
}
