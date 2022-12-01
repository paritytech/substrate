// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Collection of common consensus specific implementations

pub mod block_import;
pub mod import_queue;
pub mod metrics;

pub use block_import::{
	BlockCheckParams, BlockImport, BlockImportParams, ForkChoiceStrategy, ImportResult,
	ImportedAux, ImportedState, JustificationImport, JustificationSyncLink, StateAction,
	StorageChanges,
};
pub use import_queue::{
	import_single_block, BasicQueue, BlockImportError, BlockImportStatus, BoxBlockImport,
	BoxJustificationImport, DefaultImportQueue, ImportQueue, IncomingBlock, Link, Verifier,
};

mod longest_chain;

pub mod shared_data;

pub use longest_chain::LongestChain;
