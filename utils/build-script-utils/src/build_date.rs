// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

use std::{borrow::Cow, process::Command};

/// Add `SUBSTRATE_CLI_BUILD_DATE` to the cargo env
pub fn generate_build_date_key() {
	let build_date = match Command::new("date").args(["-u", "+%FT%TZ"]).output() {
		Ok(o) if o.status.success() => {
			let tmsp = String::from_utf8_lossy(&o.stdout).trim().to_owned();
			Cow::from(tmsp)
		},
		Ok(o) => {
			println!("cargo:warning=date command failed with status: {}", o.status);
			Cow::from("unknown")
		},
		Err(err) => {
			println!("cargo:warning=Failed to execute date command: {}", err);
			Cow::from("unknown")
		},
	};

	println!("cargo:rustc-env=SUBSTRATE_CLI_BUILD_DATE={build_date}");
}
