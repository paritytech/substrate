// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Re-exports `sp-weights` public API, and contains benchmarked weight constants specific to FRAME.

mod block_weights;
mod extrinsic_weights;
mod paritydb_weights;
mod rocksdb_weights;

pub use sp_weights::*;

/// These constants are specific to FRAME, and the current implementation of its various components.
/// For example: FRAME System, FRAME Executive, our FRAME support libraries, etc...
pub mod constants {
	pub use sp_weights::constants::*;

	// Expose the Block and Extrinsic base weights.
	pub use super::{block_weights::BlockExecutionWeight, extrinsic_weights::ExtrinsicBaseWeight};

	// Expose the DB weights.
	pub use super::{
		paritydb_weights::constants::ParityDbWeight, rocksdb_weights::constants::RocksDbWeight,
	};
}
