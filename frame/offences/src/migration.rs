// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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

use super::*;

mod deprecated {
    use crate::{Config, Perbill, OffenceDetails, SessionIndex};
    use frame_support::{decl_module, decl_storage};
    use sp_std::prelude::*;

    /// Type of data stored as a deferred offence
    pub type DeferredOffenceOf<T> = (
        Vec<OffenceDetails<<T as frame_system::Config>::AccountId, <T as Config>::IdentificationTuple>>,
        Vec<Perbill>,
        SessionIndex,
    );

    decl_storage! {
        trait Store for Module<T: Config> as Indices {
            /// Deferred reports that have been rejected by the offence handler and need to be submitted
            /// at a later time.
            pub DeferredOffences get(fn deferred_offences): Vec<DeferredOffenceOf<T>>;
        }
    }
    decl_module! {
        pub struct Module<T: Config> for enum Call where origin: T::Origin { }
    }
}

pub fn remove_deferred_storage<T: Config>() -> Weight {
    if !deprecated::DeferredOffences::<T>::exists() {
        return 0
    }

    let mut consumed = Weight::zero();
    let deferred = <deprecated::DeferredOffences<T>>::take();
    for (offences, perbill, session) in deferred.iter() {
        let weight = T::OnOffenceHandler::on_offence(&offences, &perbill, *session);
        consumed += weight;
    }

    consumed
}

#[cfg(feature = "runtime-benchmarks")]
pub fn set_deferred_offences<T: Config>(offences: Vec<DeferredOffenceOf<T>>) {
    <deprecated::DeferredOffences::<T>>::put(offences);
}

#[cfg(feature = "runtime-benchmarks")]
pub fn get_deferred_offences<T: Config>() -> Option<Vec<DeferredOffenceOf<T>>> {
    <deprecated::DeferredOffences::<T>>::try_get().ok()
}
