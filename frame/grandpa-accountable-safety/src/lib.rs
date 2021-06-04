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

#![cfg_attr(not(feature = "std"), no_std)]

use codec::{self as codec, Decode, Encode};
use sp_finality_grandpa::{
    accountable_safety::{Query, QueryResponse},
    AuthorityId, Commit, RoundNumber,
};
use sp_runtime::RuntimeDebug;
use sp_std::prelude::*;

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
    use super::*;
    use frame_support::pallet_prelude::*;
    use frame_system::pallet_prelude::*;

    #[pallet::pallet]
    #[pallet::generate_store(pub(super) trait Store)]
    pub struct Pallet<T>(_);

    #[pallet::config]
    pub trait Config: frame_system::Config {
        /// The event type of this module.
        type Event: From<Event>
            + Into<<Self as frame_system::Config>::Event>
            + IsType<<Self as frame_system::Config>::Event>;
    }

    #[pallet::storage]
    #[pallet::getter(fn accountable_safety_session)]
    pub(super) type AccountableSafetySession<T: Config> =
        StorageValue<_, StoredAccountableSafetySession<T::BlockNumber>>;

    /// For each round we track the voters asked, and then responded.
    /// Empty Vec means that we are still waiting for a reply.
    #[pallet::storage]
    #[pallet::getter(fn accountable_safety_queries)]
    pub(super) type AccountableSafetyQueries<T: Config> =
        StorageMap<_, Twox64Concat, AuthorityId, Query<T::Hash, T::BlockNumber>>;

    #[pallet::event]
    #[pallet::generate_deposit(fn deposit_event)]
    pub enum Event {
        Initiated,
    }

    #[pallet::hooks]
    impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {}
}

impl<T: Config> Pallet<T> {
    fn start_accountable_safety(
        block_not_included: (Commit<T::Hash, T::BlockNumber>, RoundNumber),
        new_block: (Commit<T::Hash, T::BlockNumber>, RoundNumber),
    ) {
        let block_not_included = (block_not_included.0.target_number, block_not_included.1);
        let state = StoredAccountableSafetySession {
            block_not_included,
            offending_block: new_block.0.target_number,
            current_round: new_block.1,
        };

        // Use `new_block` to start the protocol
        let voters = new_block.0.precommits.iter().map(|commit| &commit.id);

        AccountableSafetySession::<T>::put(state);
        for voter in voters {
            AccountableSafetyQueries::<T>::insert(voter, Query::WaitingForReply);
        }
    }

    fn update() {
        todo!();
    }

    fn add_response(
        responder: AuthorityId,
        query_response: QueryResponse<T::Hash, T::BlockNumber>,
    ) {
        // WIP: validate input
        // - check signatures
        // - check that the responder hasn't already responded
        // - check that the correct response is provided
        // - ...

        AccountableSafetyQueries::<T>::insert(responder, Query::Replied(query_response))
    }
}

#[derive(Clone, RuntimeDebug, Encode, Decode, PartialEq, Eq)]
pub struct StoredAccountableSafetySession<N> {
    /// Earlier block not included.
    pub block_not_included: (N, RoundNumber),
    /// Latter block, for which the first block isn't an ancestor.
    pub offending_block: N,
    /// The current round in the protcol. We start from the round of the offending block and walk
    /// backwards to the round after the round where the block not included was finalized.
    pub current_round: RoundNumber,
}
