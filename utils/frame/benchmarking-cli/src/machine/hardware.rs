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
use sc_sysinfo::Throughput;
use serde::{de::Visitor, Deserialize, Deserializer, Serialize, Serializer};
use sp_std::{fmt, fmt::Formatter};

/// Serializes throughput into MiBs and represents it as `f64`.
fn serialize_throughput_as_f64<S>(throughput: &Throughput, serializer: S) -> Result<S::Ok, S::Error>
where
	S: Serializer,
{
	serializer.serialize_f64(throughput.as_mibs())
}

struct ThroughputVisitor;
impl<'de> Visitor<'de> for ThroughputVisitor {
	type Value = Throughput;

	fn expecting(&self, formatter: &mut Formatter) -> fmt::Result {
		formatter.write_str("A value that is a f64.")
	}

	fn visit_f64<E>(self, value: f64) -> Result<Self::Value, E>
	where
		E: serde::de::Error,
	{
		Ok(Throughput::from_mibs(value))
	}
}

fn deserialize_throughput<'de, D>(deserializer: D) -> Result<Throughput, D::Error>
where
	D: Deserializer<'de>,
{
	Ok(deserializer.deserialize_f64(ThroughputVisitor))?
}

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
	#[serde(
		serialize_with = "serialize_throughput_as_f64",
		deserialize_with = "deserialize_throughput"
	)]
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

#[cfg(test)]
mod tests {
	use super::*;

	/// `SUBSTRATE_REFERENCE_HARDWARE` can be en- and decoded.
	#[test]
	fn json_static_data() {
		let raw = serde_json::to_string(&*SUBSTRATE_REFERENCE_HARDWARE).unwrap();
		let decoded: Requirements = serde_json::from_str(&raw).unwrap();

		assert_eq!(decoded, SUBSTRATE_REFERENCE_HARDWARE.clone());
	}
}
