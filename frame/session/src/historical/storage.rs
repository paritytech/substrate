// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

//! Validator Set Extracting an iterator from an offchain worker stored list containing historical validatorsets.
//!
//! This is used in conjunction with [`ProvingTrie`](super::ProvingTrie) and
//! the offchain indexing API.

use sp_std::prelude::*;


use super::Trait;
use super::super::{SessionIndex, Module as SessionModule};

const PREFIX: &[u8] = b"historical";
const LAST_PRUNE: &[u8] = b"historical_last_prune";

pub struct ValidatorSet<T: Trait> {
	validator_set: Vec<(T::ValidatorId, T::FullIdentification)>
}

/// Derive the key used to store the list of validators
fn derive_key<P:AsRef<[u8]>, T: Trait>(prefix: P, session_index: Vec<u8>) -> Vec<u8> {
	assert!(session_index.len() > 0);
	let prefix = prefix.as_ref();
	let mut concatenated = Vec::with_capacity(prefix.len() + 1 + session_index.len());
	concatenated.extend_from_slice(prefix);
	concatenated.push('/');
	(&mut concatenated[(prefix.len()+1)..]).extend_from_slice(session_index.as_slice());
	concatenated
}


impl<T: Trait> ValidatorSet<T> {
	/// Load the set of validators for a paritcular session index from the offchain storage.
	///
	/// If none is found or decodable given `prefix` and `session`, it will return `None`.
	/// Empty validator sets should only ever exist for genesis blocks.
	fn load_from_offchain(session_index: SessionIndex) -> Option<Self> {
		let derived_key = derive_key(STATIC_PREFIX, session_index.encode());
		let validator_set = StorageValueRef::persistent(derived_key.as_ref())
				.get::<Vec<(T::ValidatorId, T::FullIdentification)>>()
				.flatten();
		validator_set
	}

	fn as_slice(&self) -> &[(T::ValidatorId, T::FullIdentification)] {
		self.validator_set.as_slice()
	}

	fn to_vec(self) -> Vec<(T::ValidatorId, T::FullIdentification)> {
		self.validator_set
	}

	fn prune_item(everything_up_to: SessionIndex) {
		StorageValueRef::persistent(derived_key.as_ref()).clear()
	}

	fn prune() {
		let move_pruning_marker = SessionModule::current_index();
		Self::prune_older_than(move_pruning_marker);
	}

	/// Attempt to prune anything that is older than `first_to_keep`.
	fn prune_older_than(first_to_keep: SessionIndex) {
		let pruning_marker_key = derive_key(STATIC_LAST_PRUNE);
		match StorageValueRef::persistent(derived_key.as_ref())
			.mutate(|x| {
				Ok(x.encode())
		}) {
			Ok(Ok(previous)) => {
				for session_index in previous..first_to_keep {
					let derived_key = derive_key(STATIC_PREFIX, session_index.encode());
					let _ = StorageValueRef::persistent(derived_key.as_ref()).clear();
				}
			},
			Ok(Err(e)) => {}, // failed to store the value calculated by the closure
			Err(e) => {}, // failed to calculate the value to store with the given closure
		}
	}


	/// Must be called from on chain.
	fn store_current<P: AsRef<[u8]>>(prefix: P, session: SessionIndex) {
		let session_index = SessionModule::current_index();
		let derived_key = derive_key(prefix.as_ref(), session.encode());
		StorageValueRef::persistent(derived_key.as_ref()).set();
	}

	/// **Must** be called from on chain, i.e. `on_block_imported`
	fn store() {

	}



impl<T: Trait> IntoIter for ValidatorSet<T> {
	type Item=(T::ValidatorId, T::FullIdentification);
	fn into_iter(self) -> impl Iterator<Item=Self::Item> {
		self.validator_set.into_iter()
	}
}