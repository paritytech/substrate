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
    // use crate::Config;
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

pub fn migrate<T: Config>() -> Weight {
    if !deprecated::DeferredOffences::<T>::exists() {
        return 0
    }

    let limit = T::WeightSoftLimit::get();
    let mut consumed = Weight::zero();

    <deprecated::DeferredOffences<T>>::mutate(|deferred| {
        deferred.retain(|(offences, perbill, session)| {
            if consumed >= limit {
                true
            } else {
                // keep those that fail to be reported again. An error log is emitted here; this
                // should not happen if staking's `can_report` is implemented properly.
                match T::OnOffenceHandler::on_offence(&offences, &perbill, *session) {
                    Ok(weight) => {
                        consumed += weight;
                        false
                    },
                    Err(_) => {
                        log::error!(
                            target: "runtime::offences",
                            "re-submitting a deferred slash returned Err at Runtime Upgrade. \
									 This should not happen with pallet-staking",
                        );
                        true
                    },
                }
            }
        })
    });

    if <deprecated::DeferredOffences<T>>::get().len() == 0 {
        <deprecated::DeferredOffences<T>>::kill();
    }

    consumed
}
