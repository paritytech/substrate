// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

//! This module allows for inspection and instrumentation, i.e. modifying the module to alter it's
//! structure or behavior, of a wasm module.
//!
//! ## Instrumentation
//!
//! In ideal world, there would be no instrumentation. However, in the real world the execution
//! engines we use are somewhat limited in their APIs or abilities.
//!
//! To give you some examples:
//!
//! - wasmi allows reaching to non-exported mutable globals so that we could reset them. Wasmtime
//!   doesn’t support that.
//!
//!   We need to reset the globals because when we
//!   execute the Substrate Runtime, we do not drop and create the instance anew, instead
//!   we restore some selected parts of the state.
//!
//! - stack depth metering can be performed via instrumentation or deferred to the engine and say be
//!   added directly in machine code. Implementing this in machine code is rather cumbersome so
//!   instrumentation looks like a good solution.
//!
//!   Stack depth metering is needed to make a wasm blob
//!   execution deterministic, which in turn is needed by the Parachain Validation Function in
//! Polkadot.
//!
//! ## Inspection
//!
//! Inspection of a wasm module may be needed to extract some useful information, such as to extract
//! data segment snapshot, which is helpful for quickly restoring the initial state of instances.
//! Inspection can be also useful to prove that a wasm module possesses some properties, such as,
//! is free of any floating point operations, which is a useful step towards making instances
//! produced from such a module deterministic.

mod data_segments_snapshot;
mod globals_snapshot;
mod runtime_blob;

pub use data_segments_snapshot::DataSegmentsSnapshot;
pub use globals_snapshot::{ExposedMutableGlobalsSet, GlobalsSnapshot, InstanceGlobals};
pub use runtime_blob::RuntimeBlob;
