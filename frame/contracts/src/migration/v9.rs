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

//! Update `CodeStorage` with the new `determinism` field.

use crate::{
	migration::{IsFinished, Migrate, PROOF_DECODE},
	CodeHash, Config, Determinism, Pallet, Weight,
};
use codec::{Decode, Encode};
use frame_support::{
	codec, pallet_prelude::*, storage, storage_alias, traits::Get, BoundedVec, DefaultNoBound,
	Identity, StoragePrefixedMap,
};
use sp_std::{marker::PhantomData, prelude::*};

#[derive(Encode, Decode)]
struct OldPrefabWasmModule {
	#[codec(compact)]
	pub instruction_weights_version: u32,
	#[codec(compact)]
	pub initial: u32,
	#[codec(compact)]
	pub maximum: u32,
	pub code: Vec<u8>,
}

#[derive(Encode, Decode)]
struct PrefabWasmModule {
	#[codec(compact)]
	pub instruction_weights_version: u32,
	#[codec(compact)]
	pub initial: u32,
	#[codec(compact)]
	pub maximum: u32,
	pub code: Vec<u8>,
	pub determinism: Determinism,
}

#[storage_alias]
type OldCodeStorage<T: Config> = StorageMap<Pallet<T>, Identity, CodeHash<T>, OldPrefabWasmModule>;

#[storage_alias]
type CodeStorage<T: Config> = StorageMap<Pallet<T>, Identity, CodeHash<T>, PrefabWasmModule>;

#[derive(Encode, Decode, MaxEncodedLen, DefaultNoBound)]
pub struct Migration<T: Config> {
	last_key: Option<BoundedVec<u8, ConstU32<256>>>,
	_phantom: PhantomData<T>,
}

impl<T: Config> Migrate<T> for Migration<T> {
	const VERSION: u16 = 9;

	fn max_step_weight() -> Weight {
		// TODO: benchmark step
		Weight::from_parts(0, 0)
	}

	fn step(&mut self) -> (IsFinished, Option<Weight>) {
		let mut iter = if let Some(last_key) = self.last_key.take() {
			OldCodeStorage::<T>::iter_from(last_key.to_vec())
		} else {
			OldCodeStorage::<T>::iter()
		};

		if let Some((key, old)) = iter.next() {
			let module = PrefabWasmModule {
				instruction_weights_version: old.instruction_weights_version,
				initial: old.initial,
				maximum: old.maximum,
				code: old.code,
				determinism: Determinism::Enforced,
			};
			CodeStorage::<T>::insert(key, module);
			self.last_key = Some(iter.last_raw_key().to_vec().try_into().unwrap());
			(IsFinished::No, None)
		} else {
			(IsFinished::Yes, None)
		}
	}
}
