// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

use crate::error::{self, Error};
use super::RuntimeBlob;
use std::mem;
use pwasm_utils::parity_wasm::elements::Instruction;

/// This is a snapshot of data segments specialzied for a particular instantiation.
///
/// Note that this assumes that no mutable globals are used.
#[derive(Clone)]
pub struct DataSegmentsSnapshot {
	/// The list of data segments represented by (offset, contents).
	data_segments: Vec<(u32, Vec<u8>)>,
}

impl DataSegmentsSnapshot {
	/// Create a snapshot from the data segments from the module.
	pub fn take(module: &RuntimeBlob) -> error::Result<Self> {
		let data_segments = module
			.data_segments()
			.into_iter()
			.map(|mut segment| {
				// Just replace contents of the segment since the segments will be discarded later
				// anyway.
				let contents = mem::replace(segment.value_mut(), vec![]);

				let init_expr = match segment.offset() {
					Some(offset) => offset.code(),
					// Return if the segment is passive
					None => return Err(Error::SharedMemUnsupported),
				};

				// [op, End]
				if init_expr.len() != 2 {
					return Err(Error::InitializerHasTooManyExpressions);
				}
				let offset = match &init_expr[0] {
					Instruction::I32Const(v) => *v as u32,
					Instruction::GetGlobal(_) => {
						// In a valid wasm file, initializer expressions can only refer imported
						// globals.
						//
						// At the moment of writing the Substrate Runtime Interface does not provide
						// any globals. There is nothing that prevents us from supporting this
						// if/when we gain those.
						return Err(Error::ImportedGlobalsUnsupported);
					}
					insn => return Err(Error::InvalidInitializerExpression(format!("{:?}", insn))),
				};

				Ok((offset, contents))
			})
			.collect::<error::Result<Vec<_>>>()?;

		Ok(Self { data_segments })
	}

	/// Apply the given snapshot to a linear memory.
	///
	/// Linear memory interface is represented by a closure `memory_set`.
	pub fn apply<E>(
		&self,
		mut memory_set: impl FnMut(u32, &[u8]) -> Result<(), E>,
	) -> Result<(), E> {
		for (offset, contents) in &self.data_segments {
			memory_set(*offset, contents)?;
		}
		Ok(())
	}
}
