// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

use codec::{Decode, Encode, FullCodec};
use frame_support::{
	pallet_prelude::ValueQuery,
	traits::PalletInfoAccess,
	weights::Weight,
	RuntimeDebug, Blake2_128Concat,
};
use sp_std::prelude::*;

/// Type used to encode the number of references an account has.
type RefCount = u32;

/// All balance information for an account.
#[derive(Encode, Decode, Clone, PartialEq, Eq, Default, RuntimeDebug, MaxEncodedLen)]
struct AccountData<Balance> {
    free: Balance,
	reserved: Balance,
	misc_frozen: Balance,
	fee_frozen: Balance,
}

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
	/// The elections-phragmen pallet.
	type Pallet: 'static + PalletInfoAccess;

	/// System config account id
	type AccountId: 'static + FullCodec;

	/// System config index
	type Index: 'static + FullCodec + Copy;

	/// Currency balance.
	type Balance: 'static + FullCodec + Copy;
}

frame_support::generate_storage_alias!(
	System, UpgradedToU32RefCount => Value<
		bool,
		ValueQuery
	>
);

frame_support::generate_storage_alias!(
	System, UpgradedToTripleRefCount => Value<
		bool,
		ValueQuery
	>
);

frame_support::generate_storage_alias!(
	System, Account<T: V2ToV3> => Map<
		(Blake2_128Concat, T::AccountId),
		AccountInfo<T::Index, AccountData<T::Balance>>
	>
);

/// Apply the migrations from 2 to 3.
///
/// ### Warning
///
/// This function tries to infer the right migration to apply only based on whether it could
/// decode any value consistent with a state representation.
/// 
/// + If the state is fully migrated, it does nothing.
/// + If the state is in single u8 reference counting, it migrates the full state to triple
/// (u32) reference counting
/// + Otherwise, it first tries to migrate assuming the state is dual reference counting,
/// and *only if no element has been translated* tries to apply the migration from single 
/// (u32) to triple reference counting.
///
/// If unsure about the behaviour, the standalone functions below have to be preferred.
pub fn apply<T: V2ToV3>() -> Weight {
    if !<UpgradedToTripleRefCount>::get(){
        if !<UpgradedToU32RefCount>::get() {
            let _ = migrate_from_single_u8_to_triple_ref_count::<T>();
            <UpgradedToU32RefCount>::put(true);        
        } else{
            let nb_translated = migrate_from_dual_to_triple_ref_count::<T>();
            if 0 == nb_translated {
                let _ = migrate_from_single_to_triple_ref_count::<T>();
            }
        }
        <UpgradedToTripleRefCount>::put(true);
		Weight::max_value()
    } else {
		log::info!(
			target: "runtime::system",
			"Already upgraded to triple reference counting. No migration necessary."
		);
		0
	}
}

use super::*;

#[allow(dead_code)]
/// Migrate from unique `u8` reference counting to triple `u32` reference counting.
pub fn migrate_from_single_u8_to_triple_ref_count<T: V2ToV3>() -> usize {
    let mut translated : usize = 0;
    <Account::<T>>::translate::<(T::Index, u8, AccountData<T::Balance>), _>(|_key, (nonce, rc, data)| {
        translated=translated+1;
        Some(AccountInfo {
            nonce,
            consumers: rc as RefCount,
            providers: 1,
            sufficients: 0,
            data,
        })
    });
    log::info!(
        target: "runtime::system",
        "Applied migration from single u8 to triple reference counting to {:?} elements.",
        translated
    );
    translated
}

#[allow(dead_code)]
/// Migrate from unique `u32` reference counting to triple `u32` reference counting.
pub fn migrate_from_single_to_triple_ref_count<T: V2ToV3>() -> usize {
    let mut translated : usize = 0;
	<Account<T>>::translate::<(T::Index, RefCount, AccountData<T::Balance>), _>(
        |_key, (nonce, consumers, data)| {
            translated=translated+1;
            Some(AccountInfo { nonce, consumers, providers: 1, sufficients: 0, data })
        },
	);
    log::info!(
        target: "runtime::system",
        "Applied migration from single to triple reference counting to {:?} elements.",
        translated
    );  
    translated
}

#[allow(dead_code)]
/// Migrate from dual `u32` reference counting to triple `u32` reference counting.
pub fn migrate_from_dual_to_triple_ref_count<T: V2ToV3>() -> usize {
    let mut translated : usize = 0;
	<Account<T>>::translate::<(T::Index, RefCount, RefCount, AccountData<T::Balance>), _>(
        |_key, (nonce, consumers, providers, data)| {
            translated=translated+1;
            Some(AccountInfo { nonce, consumers, providers, sufficients: 0, data })
        },
	);
    log::info!(
        target: "runtime::system",
        "Applied migration from dual to triple reference counting to {:?} elements.",
        translated
    );
    translated
}