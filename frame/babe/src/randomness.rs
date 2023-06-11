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

//! Provides multiple implementations of the randomness trait based on the on-chain epoch
//! randomness collected from VRF outputs.

use super::{
	AuthorVrfRandomness, Config, EpochStart, NextRandomness, Randomness, RANDOMNESS_LENGTH,
};
use frame_support::traits::Randomness as RandomnessT;
use sp_runtime::traits::{Hash, One, Saturating};

/// Randomness usable by consensus protocols that **depend** upon finality and take action
/// based upon on-chain commitments made during the epoch before the previous epoch.
///
/// An off-chain consensus protocol requires randomness be finalized before usage, but one
/// extra epoch delay beyond `RandomnessFromOneEpochAgo` suffices, under the assumption
/// that finality never stalls for longer than one epoch.
///
/// All randomness is relative to commitments to any other inputs to the computation: If
/// Alice samples randomness near perfectly using radioactive decay, but then afterwards
/// Eve selects an arbitrary value with which to xor Alice's randomness, then Eve always
/// wins whatever game they play.
///
/// All input commitments used with `RandomnessFromTwoEpochsAgo` should come from at least
/// three epochs ago. We require BABE session keys be registered at least three epochs
/// before being used to derive `ParentBlockRandomness` for example.
///
/// All users learn `RandomnessFromTwoEpochsAgo` when epoch `current_epoch - 1` starts,
/// although some learn it a few block earlier inside epoch `current_epoch - 2`.
///
/// Adversaries with enough block producers could bias this randomness by choosing upon
/// what their block producers build at the end of epoch `current_epoch - 2` or the
/// beginning epoch `current_epoch - 1`, or skipping slots at the end of epoch
/// `current_epoch - 2`.
///
/// Adversaries should not possess many block production slots towards the beginning or
/// end of every epoch, but they possess some influence over when they possess more slots.
pub struct RandomnessFromTwoEpochsAgo<T>(sp_std::marker::PhantomData<T>);

/// Randomness usable by on-chain code that **does not depend** upon finality and takes
/// action based upon on-chain commitments made during the previous epoch.
///
/// All randomness is relative to commitments to any other inputs to the computation: If
/// Alice samples randomness near perfectly using radioactive decay, but then afterwards
/// Eve selects an arbitrary value with which to xor Alice's randomness, then Eve always
/// wins whatever game they play.
///
/// All input commitments used with `RandomnessFromOneEpochAgo` should come from at least
/// two epochs ago, although the previous epoch might work in special cases under
/// additional assumption.
///
/// All users learn `RandomnessFromOneEpochAgo` at the end of the previous epoch, although
/// some block producers learn it several block earlier.
///
/// Adversaries with enough block producers could bias this randomness by choosing upon
/// what their block producers build at either the end of the previous epoch or the
/// beginning of the current epoch, or electing to skipping some of their own block
/// production slots towards the end of the previous epoch.
///
/// Adversaries should not possess many block production slots towards the beginning or
/// end of every epoch, but they possess some influence over when they possess more slots.
///
/// As an example usage, we determine parachain auctions ending times in Polkadot using
/// `RandomnessFromOneEpochAgo` because it reduces bias from `ParentBlockRandomness` and
/// does not require the extra finality delay of `RandomnessFromTwoEpochsAgo`.
pub struct RandomnessFromOneEpochAgo<T>(sp_std::marker::PhantomData<T>);

/// Randomness produced semi-freshly with each block, but inherits limitations of
/// `RandomnessFromTwoEpochsAgo` from which it derives.
///
/// All randomness is relative to commitments to any other inputs to the computation: If
/// Alice samples randomness near perfectly using radioactive decay, but then afterwards
/// Eve selects an arbitrary value with which to xor Alice's randomness, then Eve always
/// wins whatever game they play.
///
/// As with `RandomnessFromTwoEpochsAgo`, all input commitments combined with
/// `ParentBlockRandomness` should come from at least two epoch ago, except preferably
/// not near epoch ending, and thus ideally three epochs ago.
///
/// Almost all users learn this randomness for a given block by the time they receive it's
/// parent block, which makes this randomness appear fresh enough. Yet, the block producer
/// themselves learned this randomness at the beginning of epoch `current_epoch - 2`, at
/// the same time as they learn `RandomnessFromTwoEpochsAgo`.
///
/// Aside from just biasing `RandomnessFromTwoEpochsAgo`, adversaries could also bias
/// `ParentBlockRandomness` by never announcing their block if doing so yields an
/// unfavorable randomness. As such, `ParentBlockRandomness` should be considered weaker
/// than both other randomness sources provided by BABE, but `ParentBlockRandomness`
/// remains constrained by declared staking, while a randomness source like block hash is
/// only constrained by adversaries' unknowable computational power.
///
/// As an example use, parachains could assign block production slots based upon the
/// `ParentBlockRandomness` of their relay parent or relay parent's parent, provided the
/// parachain registers collators but avoids censorship sensitive functionality like
/// slashing. Any parachain with slashing could operate BABE itself or perhaps better yet
/// a BABE-like approach that derives its `ParentBlockRandomness`, and authorizes block
/// production, based upon the relay parent's `ParentBlockRandomness` or more likely the
/// relay parent's `RandomnessFromTwoEpochsAgo`.
///
/// NOTE: there is some nuance here regarding what is current and parent randomness. If
/// you are using this trait from within the runtime (i.e. as part of block execution)
/// then the randomness provided here will always be generated from the parent block. If
/// instead you are using this randomness externally, i.e. after block execution, then
/// this randomness will be provided by the "current" block (this stems from the fact that
/// we process VRF outputs on block execution finalization, i.e. `on_finalize`).
pub struct ParentBlockRandomness<T>(sp_std::marker::PhantomData<T>);

/// Randomness produced semi-freshly with each block, but inherits limitations of
/// `RandomnessFromTwoEpochsAgo` from which it derives.
///
/// See [`ParentBlockRandomness`].
#[deprecated(note = "Should not be relied upon for correctness, \
					 will not provide fresh randomness for the current block. \
					 Please use `ParentBlockRandomness` instead.")]
pub struct CurrentBlockRandomness<T>(sp_std::marker::PhantomData<T>);

impl<T: Config> RandomnessT<T::Hash, T::BlockNumber> for RandomnessFromTwoEpochsAgo<T> {
	fn random(subject: &[u8]) -> (T::Hash, T::BlockNumber) {
		let mut subject = subject.to_vec();
		subject.reserve(RANDOMNESS_LENGTH);
		subject.extend_from_slice(&Randomness::<T>::get()[..]);

		(T::Hashing::hash(&subject[..]), EpochStart::<T>::get().0)
	}
}

impl<T: Config> RandomnessT<T::Hash, T::BlockNumber> for RandomnessFromOneEpochAgo<T> {
	fn random(subject: &[u8]) -> (T::Hash, T::BlockNumber) {
		let mut subject = subject.to_vec();
		subject.reserve(RANDOMNESS_LENGTH);
		subject.extend_from_slice(&NextRandomness::<T>::get()[..]);

		(T::Hashing::hash(&subject[..]), EpochStart::<T>::get().1)
	}
}

impl<T: Config> RandomnessT<Option<T::Hash>, T::BlockNumber> for ParentBlockRandomness<T> {
	fn random(subject: &[u8]) -> (Option<T::Hash>, T::BlockNumber) {
		let random = AuthorVrfRandomness::<T>::get().map(|random| {
			let mut subject = subject.to_vec();
			subject.reserve(RANDOMNESS_LENGTH);
			subject.extend_from_slice(&random);

			T::Hashing::hash(&subject[..])
		});

		(random, <frame_system::Pallet<T>>::block_number().saturating_sub(One::one()))
	}
}

#[allow(deprecated)]
impl<T: Config> RandomnessT<Option<T::Hash>, T::BlockNumber> for CurrentBlockRandomness<T> {
	fn random(subject: &[u8]) -> (Option<T::Hash>, T::BlockNumber) {
		let (random, _) = ParentBlockRandomness::<T>::random(subject);
		(random, <frame_system::Pallet<T>>::block_number())
	}
}
