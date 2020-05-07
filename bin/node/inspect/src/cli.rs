// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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
//! Structs to easily compose inspect sub-command for CLI.

use std::fmt::Debug;
use sc_cli::{ImportParams, SharedParams};
use structopt::StructOpt;

/// The `inspect` command used to print decoded chain data.
#[derive(Debug, StructOpt, Clone)]
pub struct InspectCmd {
	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub command: InspectSubCmd,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub import_params: ImportParams,
}

/// A possible inspect sub-commands.
#[derive(Debug, StructOpt, Clone)]
pub enum InspectSubCmd {
	/// Decode block with native version of runtime and print out the details.
	Block {
		/// Address of the block to print out.
		///
		/// Can be either a block hash (no 0x prefix) or a number to retrieve existing block,
		/// or a 0x-prefixed bytes hex string, representing SCALE encoding of
		/// a block.
		#[structopt(value_name = "HASH or NUMBER or BYTES")]
		input: String,
	},
	/// Decode extrinsic with native version of runtime and print out the details.
	Extrinsic {
		/// Address of an extrinsic to print out.
		///
		/// Can be either a block hash (no 0x prefix) or number and the index, in the form
		/// of `{block}:{index}` or a 0x-prefixed bytes hex string,
		/// representing SCALE encoding of an extrinsic.
		#[structopt(value_name = "BLOCK:INDEX or BYTES")]
		input: String,
	},
}
