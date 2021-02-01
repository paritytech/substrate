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

use std::fmt::Debug;
use sc_service::Configuration;

#[derive(Debug, structopt::StructOpt)]
pub struct DruRunCmd {
	#[structopt(short, long)]
	pub pallet: String,
}

impl DruRunCmd {
	pub async fn run(&self, config: Configuration) {
		let ext = remote_externalities::Builder::default().build().await;
		let executor = NativeExecutor::<ExecDispatch>::new(
			wasm_method,
			self.heap_pages,
			2, // The runtime instances cache size.
		);
		let backend = state

		let mut changes = Default::default();
		let weight = sp_state_machine::StateMachine::<_, _, _, _>::new(
			state,
			None,
			changes,
			executor,
			"DryRunRuntimeUpgrade_dryrun_runtime_upgrade",
			vec![],
			Extensions::default(),
			&sp_state_machine::backend::BackendRuntimeCode::new(&state).runtime_code()?,
			sp_core::testing::TaskExecutor::new(),
		)
	}
}
