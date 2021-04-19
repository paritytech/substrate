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

use super::Config;
use frame_support::{storage::StorageValue, traits::Get, weights::Weight};
use sp_staking::offence::OnOffenceHandler;

mod deprecated {
    use crate::{Config, OffenceDetails, Perbill, SessionIndex};
    use frame_support::{sp_std::marker::PhantomData, storage::generator::StorageValue};
    use sp_std::vec::Vec;

    /// Type of data stored as a deferred offence
    pub type DeferredOffenceOf<T> = (
        Vec<
            OffenceDetails<
                <T as frame_system::Config>::AccountId,
                <T as Config>::IdentificationTuple,
            >,
        >,
        Vec<Perbill>,
        SessionIndex,
    );

    /// Deferred reports that have been rejected by the offence handler and need to be submitted
    /// at a later time.
    pub struct DeferredOffences<T: Config>(PhantomData<T>);

    impl<T: Config> StorageValue<Vec<DeferredOffenceOf<T>>> for DeferredOffences<T> {
        type Query = Vec<DeferredOffenceOf<T>>;
        fn module_prefix() -> &'static [u8] {
            b"Offences"
        }
        fn storage_prefix() -> &'static [u8] {
            b"DeferredOffences"
        }
        fn from_optional_value_to_query(v: Option<Vec<DeferredOffenceOf<T>>>) -> Self::Query {
            v.unwrap_or_else(|| Default::default())
        }
        fn from_query_to_optional_value(v: Self::Query) -> Option<Vec<DeferredOffenceOf<T>>> {
            Some(v)
        }
    }
}

pub fn remove_deferred_storage<T: Config>() -> Weight {
    let mut weight = T::DbWeight::get().reads_writes(1, 1);
    let deferred = <deprecated::DeferredOffences<T>>::take();
    log::info!(target: "runtime::offences", "have {} deferred offences, applying.", deferred.len());
    for (offences, perbill, session) in deferred.iter() {
        let consumed = T::OnOffenceHandler::on_offence(&offences, &perbill, *session);
        weight = weight.saturating_add(consumed);
    }

    weight
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::mock::{new_test_ext, with_on_offence_fractions, Offences, Runtime as T, System};
    use frame_support::traits::OnRuntimeUpgrade;
    use sp_runtime::Perbill;
    use sp_staking::offence::OffenceDetails;

    #[test]
    fn should_resubmit_deferred_offences() {
        new_test_ext().execute_with(|| {
            // given
            assert_eq!(<deprecated::DeferredOffences<T>>::get().len(), 0);
            with_on_offence_fractions(|f| {
                assert_eq!(f.clone(), vec![]);
            });

            let offence_details = OffenceDetails::<
                <T as frame_system::Config>::AccountId,
                <T as Config>::IdentificationTuple,
            > {
                offender: 5,
                reporters: vec![],
            };

            // push deferred offence
            <deprecated::DeferredOffences<T>>::mutate(|d| {
                d.push((
                    vec![offence_details],
                    vec![Perbill::from_percent(5 + 1 * 100 / 5)],
                    1,
                ))
            });

            // when
            assert_eq!(
                Offences::on_runtime_upgrade(),
                <T as frame_system::Config>::DbWeight::get().reads_writes(1, 2),
            );

            // then
            assert_eq!(<deprecated::DeferredOffences<T>>::get().len(), 0);
            with_on_offence_fractions(|f| {
                assert_eq!(f.clone(), vec![Perbill::from_percent(5 + 1 * 100 / 5)]);
            });

            // No events emitted
            assert_eq!(System::events().len(), 0);
        })
    }
}
