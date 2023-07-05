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

//! Authorship tracking for FRAME runtimes.
//!
//! This tracks the current author of the block.

#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::traits::FindAuthor;
use sp_std::prelude::*;

pub use pallet::*;

/// An event handler for the authorship pallet. There is a dummy implementation
/// for `()`, which does nothing.
#[impl_trait_for_tuples::impl_for_tuples(30)]
pub trait EventHandler<Author, BlockNumber> {
	/// Note that the given account ID is the author of the current block.
	fn note_author(author: Author);
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// Find the author of a block.
		type FindAuthor: FindAuthor<Self::AccountId>;
		/// An event handler for authored blocks.
		type EventHandler: EventHandler<Self::AccountId, Self::BlockNumber>;
	}

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_initialize(_: T::BlockNumber) -> Weight {
			if let Some(author) = Self::author() {
				T::EventHandler::note_author(author);
			}

			Weight::zero()
		}

		fn on_finalize(_: T::BlockNumber) {
			// ensure we never go to trie with these values.
			<Author<T>>::kill();
		}
	}

	#[pallet::storage]
	/// Author of current block.
	pub(super) type Author<T: Config> = StorageValue<_, T::AccountId, OptionQuery>;
}

impl<T: Config> Pallet<T> {
	/// Fetch the author of the block.
	///
	/// This is safe to invoke in `on_initialize` implementations, as well
	/// as afterwards.
	pub fn author() -> Option<T::AccountId> {
		// Check the memorized storage value.
		if let Some(author) = <Author<T>>::get() {
			return Some(author)
		}

		let digest = <frame_system::Pallet<T>>::digest();
		let pre_runtime_digests = digest.logs.iter().filter_map(|d| d.as_pre_runtime());
		T::FindAuthor::find_author(pre_runtime_digests).map(|a| {
			<Author<T>>::put(&a);
			a
		})
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate as pallet_authorship;
	use codec::{Decode, Encode};
	use frame_support::{
		traits::{ConstU32, ConstU64},
		ConsensusEngineId,
	};
	use sp_core::H256;
	use sp_runtime::{
		generic::DigestItem,
		testing::Header,
		traits::{BlakeTwo256, Header as HeaderT, IdentityLookup},
	};

	type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
	type Block = frame_system::mocking::MockBlock<Test>;

	frame_support::construct_runtime!(
		pub enum Test where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic,
		{
			System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
			Authorship: pallet_authorship::{Pallet, Storage},
		}
	);

	impl frame_system::Config for Test {
		type BaseCallFilter = frame_support::traits::Everything;
		type BlockWeights = ();
		type BlockLength = ();
		type DbWeight = ();
		type RuntimeOrigin = RuntimeOrigin;
		type Index = u64;
		type BlockNumber = u64;
		type RuntimeCall = RuntimeCall;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type RuntimeEvent = RuntimeEvent;
		type BlockHashCount = ConstU64<250>;
		type Version = ();
		type PalletInfo = PalletInfo;
		type AccountData = ();
		type OnNewAccount = ();
		type OnKilledAccount = ();
		type SystemWeightInfo = ();
		type SS58Prefix = ();
		type OnSetCode = ();
		type MaxConsumers = ConstU32<16>;
	}

	impl pallet::Config for Test {
		type FindAuthor = AuthorGiven;
		type EventHandler = ();
	}

	const TEST_ID: ConsensusEngineId = [1, 2, 3, 4];

	pub struct AuthorGiven;

	impl FindAuthor<u64> for AuthorGiven {
		fn find_author<'a, I>(digests: I) -> Option<u64>
		where
			I: 'a + IntoIterator<Item = (ConsensusEngineId, &'a [u8])>,
		{
			for (id, mut data) in digests {
				if id == TEST_ID {
					return u64::decode(&mut data).ok()
				}
			}

			None
		}
	}

	fn seal_header(mut header: Header, author: u64) -> Header {
		{
			let digest = header.digest_mut();
			digest.logs.push(DigestItem::PreRuntime(TEST_ID, author.encode()));
			digest.logs.push(DigestItem::Seal(TEST_ID, author.encode()));
		}

		header
	}

	fn create_header(number: u64, parent_hash: H256, state_root: H256) -> Header {
		Header::new(number, Default::default(), state_root, parent_hash, Default::default())
	}

	fn new_test_ext() -> sp_io::TestExternalities {
		let t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		t.into()
	}

	#[test]
	fn sets_author_lazily() {
		new_test_ext().execute_with(|| {
			let author = 42;
			let mut header =
				seal_header(create_header(1, Default::default(), [1; 32].into()), author);

			header.digest_mut().pop(); // pop the seal off.
			System::reset_events();
			System::initialize(&1, &Default::default(), header.digest());

			assert_eq!(Authorship::author(), Some(author));
		});
	}
}
