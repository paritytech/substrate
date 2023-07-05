// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Contains types to define hardware requirements.

use lazy_static::lazy_static;
use sc_sysinfo::Requirements;

lazy_static! {
	/// The hardware requirements as measured on reference hardware.
	///
	/// These values are provided by Parity, however it is possible
	/// to use your own requirements if you are running a custom chain.
	pub static ref SUBSTRATE_REFERENCE_HARDWARE: Requirements = {
		let raw = include_bytes!("reference_hardware.json").as_slice();
		serde_json::from_slice(raw).expect("Hardcoded data is known good; qed")
	};
}

#[cfg(test)]
mod tests {
	use super::*;
	use sc_sysinfo::{Metric, Requirement, Requirements, Throughput};

	/// `SUBSTRATE_REFERENCE_HARDWARE` can be decoded.
	#[test]
	fn json_static_data() {
		let raw = serde_json::to_string(&*SUBSTRATE_REFERENCE_HARDWARE).unwrap();
		let decoded: Requirements = serde_json::from_str(&raw).unwrap();

		assert_eq!(decoded, SUBSTRATE_REFERENCE_HARDWARE.clone());
	}

	/// The hard-coded values are correct.
	#[test]
	fn json_static_data_is_correct() {
		assert_eq!(
			*SUBSTRATE_REFERENCE_HARDWARE,
			Requirements(vec![
				Requirement { metric: Metric::Blake2256, minimum: Throughput::from_mibs(783.27) },
				Requirement {
					metric: Metric::Sr25519Verify,
					minimum: Throughput::from_kibs(560.670000128),
				},
				Requirement {
					metric: Metric::MemCopy,
					minimum: Throughput::from_gibs(11.4925205078125003),
				},
				Requirement { metric: Metric::DiskSeqWrite, minimum: Throughput::from_mibs(950.0) },
				Requirement { metric: Metric::DiskRndWrite, minimum: Throughput::from_mibs(420.0) },
			])
		);
	}
}
