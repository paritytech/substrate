// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! The transaction's event returned as json compatible object.

use serde::{ser::SerializeStruct, Deserialize, Serialize, Serializer};
use sp_version::RuntimeVersion;

/// The transaction could not be processed due to an error.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RuntimeErrorEvent {
	/// Reason of the error.
	pub error: String,
}

/// The transaction could not be processed due to an error.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RuntimeVersionEvent {
	/// Reason of the error.
	pub spec: RuntimeVersion,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(tag = "type")]
pub enum RuntimeEvent {
	Valid(RuntimeVersionEvent),
	Invalid(RuntimeErrorEvent),
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Initialized<Hash> {
	/// The hash of the imported block.
	pub finalized_block_hash: Hash,
	#[serde(default)]
	pub finalized_block_runtime: Option<RuntimeEvent>,
	#[serde(default)]
	runtime_updates: bool,
}

impl<Hash: Serialize> Serialize for Initialized<Hash> {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		if self.runtime_updates {
			let mut state = serializer.serialize_struct("Initialized", 2)?;
			state.serialize_field("finalizedBlockHash", &self.finalized_block_hash)?;
			state.serialize_field("finalizedBlockRuntime", &self.finalized_block_runtime)?;
			state.end()
		} else {
			let mut state = serializer.serialize_struct("Initialized", 2)?;
			state.serialize_field("finalizedBlockHash", &self.finalized_block_hash)?;
			state.end()
		}
	}
}

/// The transaction was included in a block of the chain.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NewBlock<Hash> {
	/// The hash of the imported block.
	pub block_hash: Hash,
	/// The parent hash of the imported block.
	pub parent_block_hash: Hash,
	pub new_runtime: Option<RuntimeEvent>,
	runtime_updates: bool,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct BestBlockChanged<Hash> {
	pub best_block_hash: Hash,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Finalized<Hash> {
	pub finalized_block_hashes: Vec<Hash>,
	pub pruned_block_hashes: Vec<Hash>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(tag = "event")]
pub enum FollowEvent<Hash> {
	Initialized(Initialized<Hash>),
	NewBlock(NewBlock<Hash>),
	BestBlockChanged(BestBlockChanged<Hash>),
	Finalized(Finalized<Hash>),
	Stop,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(tag = "event", content = "value")]
pub enum BodyEvent<Body> {
	Done(Body),
	Inaccessible,
	Disjoint,
}

mod tests {
	use super::*;

	#[test]
	fn follow_initialized_event_no_runtime() {
		// Runtime flag is false.
		let event: FollowEvent<String> = FollowEvent::Initialized(Initialized {
			finalized_block_hash: "0x1".into(),
			finalized_block_runtime: None,
			runtime_updates: false,
		});

		let ser = serde_json::to_string(&event).unwrap();
		let exp = r#"{"event":"initialized","finalizedBlockHash":"0x1"}"#;
		assert_eq!(ser, exp);

		let event_dec: FollowEvent<String> = serde_json::from_str(exp).unwrap();
		assert_eq!(event_dec, event);
	}

	#[test]
	fn follow_initialized_event_with_runtime() {
		// Runtime flag is true, block runtime must always be reported for this event.
		let runtime = RuntimeVersion {
			spec_name: "ABC".into(),
			impl_name: "Impl".into(),
			spec_version: 1,
			..Default::default()
		};

		let runtime_event = RuntimeEvent::Valid(RuntimeVersionEvent { spec: runtime });
		let mut initialized = Initialized {
			finalized_block_hash: "0x1".into(),
			finalized_block_runtime: Some(runtime_event),
			runtime_updates: true,
		};
		let event: FollowEvent<String> = FollowEvent::Initialized(initialized.clone());

		let ser = serde_json::to_string(&event).unwrap();
		let exp = concat!(
			r#"{"event":"initialized","finalizedBlockHash":"0x1","#,
			r#""finalizedBlockRuntime":{"type":"valid","spec":{"specName":"ABC","implName":"Impl","authoringVersion":0,"#,
			r#""specVersion":1,"implVersion":0,"apis":[],"transactionVersion":0,"stateVersion":0}}}"#,
		);
		assert_eq!(ser, exp);

		let event_dec: FollowEvent<String> = serde_json::from_str(exp).unwrap();
		// The `runtime_updates` field is used for serialization purposes.
		initialized.runtime_updates = false;
		assert!(matches!(
			event_dec, FollowEvent::Initialized(ref dec) if dec == &initialized
		));
	}
}
