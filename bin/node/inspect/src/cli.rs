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

//! Structs to easily compose inspect sub-command for CLI.

use sc_cli::{ImportParams, SharedParams};

/// The `inspect` command used to print decoded chain data.
#[derive(Debug, clap::Parser)]
pub struct InspectCmd {
	#[allow(missing_docs)]
	#[clap(subcommand)]
	pub command: InspectSubCmd,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub import_params: ImportParams,
}

/// A possible inspect sub-commands.
#[derive(Debug, clap::Subcommand)]
pub enum InspectSubCmd {
	/// Decode block with native version of runtime and print out the details.
	Block {
		/// Address of the block to print out.
		///
		/// Can be either a block hash (no 0x prefix) or a number to retrieve existing block,
		/// or a 0x-prefixed bytes hex string, representing SCALE encoding of
		/// a block.
		#[arg(value_name = "HASH or NUMBER or BYTES")]
		input: String,
	},
	/// Decode extrinsic with native version of runtime and print out the details.
	Extrinsic {
		/// Address of an extrinsic to print out.
		///
		/// Can be either a block hash (no 0x prefix) or number and the index, in the form
		/// of `{block}:{index}` or a 0x-prefixed bytes hex string,
		/// representing SCALE encoding of an extrinsic.
		#[arg(value_name = "BLOCK:INDEX or BYTES")]
		input: String,
	},
}
