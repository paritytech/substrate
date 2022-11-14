// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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
use serde::{Deserialize, Serialize};
use std::fmt;

lazy_static! {
	/// The hardware requirements as measured on reference hardware.
	///
	/// These values are provided by Parity, however it is possible
	/// to use your own requirements if you are running a custom chain.
	///
	/// The reference hardware is describe here:
	/// <https://wiki.polkadot.network/docs/maintain-guides-how-to-validate-polkadot>
	pub static ref SUBSTRATE_REFERENCE_HARDWARE: Requirements = {
		let raw = include_bytes!("reference_hardware.json").as_slice();
		serde_json::from_slice(raw).expect("Hardcoded data is known good; qed")
	};
}

/// Multiple requirements for the hardware.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
pub struct Requirements(pub Vec<Requirement>);

/// A single requirement for the hardware.
#[derive(Deserialize, Serialize, Debug, Clone, Copy, PartialEq)]
pub struct Requirement {
	/// The metric to measure.
	pub metric: Metric,
	/// The minimal throughput that needs to be archived for this requirement.
	pub minimum: Throughput,
}

/// A single hardware metric.
///
/// The implementation of these is in `sc-sysinfo`.
#[derive(Deserialize, Serialize, Debug, Clone, Copy, PartialEq)]
pub enum Metric {
	/// SR25519 signature verification.
	Sr25519Verify,
	/// Blake2-256 hashing algorithm.
	Blake2256,
	/// Copying data in RAM.
	MemCopy,
	/// Disk sequential write.
	DiskSeqWrite,
	/// Disk random write.
	DiskRndWrite,
}

/// Throughput as measured in bytes per second.
#[derive(Deserialize, Serialize, Debug, Clone, Copy, PartialEq)]
pub enum Throughput {
	/// KiB/s
	KiBs(f64),
	/// MiB/s
	MiBs(f64),
	/// GiB/s
	GiBs(f64),
}

impl Metric {
	/// The category of the metric.
	pub fn category(&self) -> &'static str {
		match self {
			Self::Sr25519Verify | Self::Blake2256 => "CPU",
			Self::MemCopy => "Memory",
			Self::DiskSeqWrite | Self::DiskRndWrite => "Disk",
		}
	}

	/// The name of the metric. It is always prefixed by the [`self::category()`].
	pub fn name(&self) -> &'static str {
		match self {
			Self::Sr25519Verify => "SR25519-Verify",
			Self::Blake2256 => "BLAKE2-256",
			Self::MemCopy => "Copy",
			Self::DiskSeqWrite => "Seq Write",
			Self::DiskRndWrite => "Rnd Write",
		}
	}
}

const KIBIBYTE: f64 = 1024.0;

impl Throughput {
	/// The unit of the metric.
	pub fn unit(&self) -> &'static str {
		match self {
			Self::KiBs(_) => "KiB/s",
			Self::MiBs(_) => "MiB/s",
			Self::GiBs(_) => "GiB/s",
		}
	}

	/// [`Self`] as number of byte/s.
	pub fn to_bs(&self) -> f64 {
		self.to_kibs() * KIBIBYTE
	}

	/// [`Self`] as number of kibibyte/s.
	pub fn to_kibs(&self) -> f64 {
		self.to_mibs() * KIBIBYTE
	}

	/// [`Self`] as number of mebibyte/s.
	pub fn to_mibs(&self) -> f64 {
		self.to_gibs() * KIBIBYTE
	}

	/// [`Self`] as number of gibibyte/s.
	pub fn to_gibs(&self) -> f64 {
		match self {
			Self::KiBs(k) => *k / (KIBIBYTE * KIBIBYTE),
			Self::MiBs(m) => *m / KIBIBYTE,
			Self::GiBs(g) => *g,
		}
	}

	/// Normalizes [`Self`] to use the larges unit possible.
	pub fn normalize(&self) -> Self {
		let bs = self.to_bs();

		if bs >= KIBIBYTE * KIBIBYTE * KIBIBYTE {
			Self::GiBs(self.to_gibs())
		} else if bs >= KIBIBYTE * KIBIBYTE {
			Self::MiBs(self.to_mibs())
		} else {
			Self::KiBs(self.to_kibs())
		}
	}
}

impl fmt::Display for Throughput {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let normalized = self.normalize();
		match normalized {
			Self::KiBs(s) | Self::MiBs(s) | Self::GiBs(s) =>
				write!(f, "{:.2?} {}", s, normalized.unit()),
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_runtime::assert_eq_error_rate_float;

	/// `SUBSTRATE_REFERENCE_HARDWARE` can be en- and decoded.
	#[test]
	fn json_static_data() {
		let raw = serde_json::to_string(&*SUBSTRATE_REFERENCE_HARDWARE).unwrap();
		let decoded: Requirements = serde_json::from_str(&raw).unwrap();

		assert_eq!(decoded, SUBSTRATE_REFERENCE_HARDWARE.clone());
	}

	/// Test the [`Throughput`].
	#[test]
	fn throughput_works() {
		/// Float precision.
		const EPS: f64 = 0.1;
		let gib = Throughput::GiBs(14.324);

		assert_eq_error_rate_float!(14.324, gib.to_gibs(), EPS);
		assert_eq_error_rate_float!(14667.776, gib.to_mibs(), EPS);
		assert_eq_error_rate_float!(14667.776 * 1024.0, gib.to_kibs(), EPS);
		assert_eq!("14.32 GiB/s", gib.to_string());
		assert_eq!("14.32 GiB/s", gib.normalize().to_string());

		let mib = Throughput::MiBs(1029.0);
		assert_eq!("1.00 GiB/s", mib.to_string());
	}
}
