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

use clap::Args;
use std::str::FromStr;

/// Parameters used to config runtime.
#[derive(Debug, Clone, Args)]
pub struct RuntimeParams {
	/// The size of the instances cache for each runtime. The values higher than 256 are illegal.
	#[arg(long, default_value_t = 8, value_parser = parse_max_runtime_instances)]
	pub max_runtime_instances: usize,

	/// Maximum number of different runtimes that can be cached.
	#[arg(long, default_value_t = 2)]
	pub runtime_cache_size: u8,
}

fn parse_max_runtime_instances(s: &str) -> Result<usize, String> {
	let max_runtime_instances = usize::from_str(s)
		.map_err(|_err| format!("Illegal `--max-runtime-instances` value: {s}"))?;

	if max_runtime_instances > 256 {
		Err(format!("Illegal `--max-runtime-instances` value: {max_runtime_instances} is more than the allowed maximum of `256` "))
	} else {
		Ok(max_runtime_instances)
	}
}
