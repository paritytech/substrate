// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use super::InstanceWrapper;
use sc_executor_common::error::{Result, Error};
use sp_wasm_interface::Value;
use crate::imports::{into_value, into_wasmtime_val};

/// Saved value of particular exported global.
struct SavedValue {
	/// Index of the export.
	index: usize,
	/// Global value.
	value: Value,
}

/// A snapshot of a global variables values. This snapshot can be used later for restoring the
/// values to the preserved state.
///
/// Technically, a snapshot stores only values of mutable global variables. This is because
/// immutable global variables always have the same values.
pub struct GlobalsSnapshot(Vec<SavedValue>);

impl GlobalsSnapshot {
	/// Take a snapshot of global variables for a given instance.
	pub fn take(instance_wrapper: &InstanceWrapper) -> Result<Self> {
		let data = instance_wrapper.instance
			.exports()
			.enumerate()
			.filter_map(|(index, export)| {
				if export.name().starts_with("exported_internal_global") {
					export.into_global().map(
						|g| SavedValue { index, value: into_value(g.get()) }
					)
				} else { None }
			})
			.collect::<Vec<_>>();

		Ok(Self(data))
	}

	/// Apply the snapshot to the given instance.
	///
	/// This instance must be the same that was used for creation of this snapshot.
	pub fn apply(&self, instance_wrapper: &InstanceWrapper) -> Result<()> {
		// This is a pointer over saved items, it moves forward when the loop value below takes over it's current value.
		// Since both pointers (`current` and `index` below) are over ordered lists, they eventually hit all
		// equal referenced values.
		let mut current = 0;
		for (index, export) in instance_wrapper.instance.exports().enumerate() {
			if current >= self.0.len() { break; }
			let current_saved = &self.0[current];
			if index < current_saved.index { continue; }
			else if index > current_saved.index { current += 1; continue; }
			else {
				export.into_global()
					.ok_or_else(|| Error::Other(
						"Wrong instance in GlobalsSnapshot::apply: what should be global is not global.".to_string()
					))?
					.set(into_wasmtime_val(current_saved.value))
					.map_err(|_e| Error::Other(
						"Wrong instance in GlobalsSnapshot::apply: global saved type does not matched applied.".to_string()
					))?;
			}
		}

		Ok(())
	}
}
