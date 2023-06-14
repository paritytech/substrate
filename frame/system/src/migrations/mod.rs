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

//! Migrate the reference counting state.

use super::LOG_TARGET;
use crate::{Config, Pallet};
use codec::{Decode, Encode, FullCodec};
use frame_support::{
	pallet_prelude::ValueQuery, traits::PalletInfoAccess, weights::Weight, Blake2_128Concat,
	RuntimeDebug,
};
use sp_std::prelude::*;

/// Type used to encode the number of references an account has.
type RefCount = u32;

/// Information of an account.
#[derive(Clone, Eq, PartialEq, Default, RuntimeDebug, Encode, Decode)]
struct AccountInfo<Index, AccountData> {
	nonce: Index,
	consumers: RefCount,
	providers: RefCount,
	sufficients: RefCount,
	data: AccountData,
}

/// Trait to implement to give information about types used for migration
pub trait V2ToV3 {
	/// The system pallet.
	type Pallet: 'static + PalletInfoAccess;

	/// System config account id
	type AccountId: 'static + FullCodec;

	/// System config index
	type Index: 'static + FullCodec + Copy;

	/// System config account data
	type AccountData: 'static + FullCodec;
}

#[frame_support::storage_alias]
type UpgradedToU32RefCount<T: Config> = StorageValue<Pallet<T>, bool, ValueQuery>;

#[frame_support::storage_alias]
type UpgradedToTripleRefCount<T: Config> = StorageValue<Pallet<T>, bool, ValueQuery>;

#[frame_support::storage_alias]
type Account<V, T: Config> = StorageMap<
	Pallet<T>,
	Blake2_128Concat,
	<V as V2ToV3>::AccountId,
	AccountInfo<<V as V2ToV3>::Index, <V as V2ToV3>::AccountData>,
>;

/// Migrate from unique `u8` reference counting to triple `u32` reference counting.
pub fn migrate_from_single_u8_to_triple_ref_count<V: V2ToV3, T: Config>() -> Weight {
	let mut translated: usize = 0;
	<Account<V, T>>::translate::<(V::Index, u8, V::AccountData), _>(|_key, (nonce, rc, data)| {
		translated += 1;
		Some(AccountInfo { nonce, consumers: rc as RefCount, providers: 1, sufficients: 0, data })
	});
	log::info!(
		target: LOG_TARGET,
		"Applied migration from single u8 to triple reference counting to {:?} elements.",
		translated
	);
	<UpgradedToU32RefCount<T>>::put(true);
	<UpgradedToTripleRefCount<T>>::put(true);
	Weight::MAX
}

/// Migrate from unique `u32` reference counting to triple `u32` reference counting.
pub fn migrate_from_single_to_triple_ref_count<V: V2ToV3, T: Config>() -> Weight {
	let mut translated: usize = 0;
	<Account<V, T>>::translate::<(V::Index, RefCount, V::AccountData), _>(
		|_key, (nonce, consumers, data)| {
			translated += 1;
			Some(AccountInfo { nonce, consumers, providers: 1, sufficients: 0, data })
		},
	);
	log::info!(
		target: LOG_TARGET,
		"Applied migration from single to triple reference counting to {:?} elements.",
		translated
	);
	<UpgradedToTripleRefCount<T>>::put(true);
	Weight::MAX
}

/// Migrate from dual `u32` reference counting to triple `u32` reference counting.
pub fn migrate_from_dual_to_triple_ref_count<V: V2ToV3, T: Config>() -> Weight {
	let mut translated: usize = 0;
	<Account<V, T>>::translate::<(V::Index, RefCount, RefCount, V::AccountData), _>(
		|_key, (nonce, consumers, providers, data)| {
			translated += 1;
			Some(AccountInfo { nonce, consumers, providers, sufficients: 0, data })
		},
	);
	log::info!(
		target: LOG_TARGET,
		"Applied migration from dual to triple reference counting to {:?} elements.",
		translated
	);
	<UpgradedToTripleRefCount<T>>::put(true);
	Weight::MAX
}
