// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! System manager: Handles all of the top-level stuff; executing block/transaction, setting code
//! and depositing logs.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg_attr(test, macro_use)] extern crate substrate_runtime_std as rstd;
#[macro_use] extern crate substrate_runtime_support as runtime_support;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_codec as codec;
extern crate substrate_runtime_primitives as primitives;
extern crate substrate_runtime_system as system;

#[cfg(feature = "std")] extern crate serde;

//extern crate safe_mix;

use rstd::prelude::*;
use rstd::marker::PhantomData;
use primitives::{Zero, One, Headery, Blocky, Checkable, Applyable, CheckEqual, Hashing, Executable};
use codec::Slicable;
//use runtime_support::{Hashable, StorageValue, StorageMap};

//use primitives::{AuthorityId, Hash, BlockNumber, Header, Log};
//use primitives::block::{generic, Number as BlockNumber, Header, Log};

//use safe_mix::TripletMix;

pub struct Executive<
	Unchecked,
	Checked,
	System,
	Block,
	Finalisation,
>(PhantomData<(Unchecked, Checked, System, Block, Finalisation)>);

impl<
	Unchecked: Checkable<
		CheckedType = Checked
	> + PartialEq + Eq + Clone + Slicable,
	Checked: Applyable<
		IndexType = System::Index,
		AccountIdType = System::AccountId
	>,
	System: system::Trait,
	Block: Blocky<
		Extrinsic = Unchecked,
		Header = System::Header
	>,
	Finalisation: Executable,
> Executive<Unchecked, Checked, System, Block, Finalisation> {
	/// Start the execution of a particular block.
	pub fn initialise_block(header: &System::Header) {
		<system::Module<System>>::initialise(header.number(), header.parent_hash(), header.extrinsics_root());
	}

	fn initial_checks(block: &Block) {
		let header = block.header();

		// check parent_hash is correct.
		let n = header.number().clone();
		assert!(
			n > System::BlockNumber::zero() && <system::Module<System>>::block_hash(n - System::BlockNumber::one()) == *header.parent_hash(),
			"Parent hash should be valid."
		);

		// check transaction trie root represents the transactions.
		let txs = block.extrinsics().iter().map(Slicable::encode).collect::<Vec<_>>();
		let txs = txs.iter().map(Vec::as_slice).collect::<Vec<_>>();
		let txs_root = System::Hashing::enumerated_trie_root(&txs);
		header.extrinsics_root().check_equal(&txs_root);
		assert!(header.extrinsics_root() == &txs_root, "Transaction trie root must be valid.");
	}

	/// Actually execute all transitioning for `block`.
	pub fn execute_block(block: Block) {
		Self::initialise_block(block.header());

		// any initial checks
		Self::initial_checks(&block);

		// execute transactions
		let (header, extrinsics) = block.deconstruct();
		extrinsics.into_iter().for_each(Self::apply_extrinsic);

		// post-transactional book-keeping.
		Finalisation::execute();

		// any final checks
		Self::final_checks(&header);

		// any stuff that we do after taking the storage root.
		Self::post_finalise(&header);
	}

	/// Finalise the block - it is up the caller to ensure that all header fields are valid
	/// except state-root.
	pub fn finalise_block() -> System::Header {
		Finalisation::execute();

		let header = <system::Module<System>>::finalise();
		Self::post_finalise(&header);

		header
	}

	/// Apply outside of the block execution function.
	/// This doesn't attempt to validate anything regarding the block.
	pub fn apply_extrinsic(utx: Unchecked) {
		// Verify the signature is good.
		let tx = match utx.check() {
			Ok(tx) => tx,
			Err(_) => panic!("All transactions should be properly signed"),
		};

		{
			// check nonce
			let expected_nonce = <system::Module<System>>::account_index(tx.sender());
			assert!(tx.index() == &expected_nonce, "All transactions should have the correct nonce");

			// increment nonce in storage
			<system::Module<System>>::inc_account_index(tx.sender());
		}

		// decode parameters and dispatch
		tx.apply();
	}

	fn final_checks(header: &System::Header) {
		// check digest
		assert!(header.digest() == &<system::Module<System>>::digest());

		// remove temporaries.
		<system::Module<System>>::finalise();

		// check storage root.
		let storage_root = System::Hashing::storage_root();
		header.state_root().check_equal(&storage_root);
		assert!(header.state_root() == &storage_root, "Storage root must match that calculated.");
	}

	fn post_finalise(header: &System::Header) {
		// store the header hash in storage; we can't do it before otherwise there would be a
		// cyclic dependency.
		<system::Module<System>>::record_block_hash(header)
	}
}
/*
#[cfg(test)]
mod tests {
	use super::*;
	use super::internal::*;

	use runtime_io::{with_externalities, twox_128, TestExternalities};
	use runtime_support::StorageValue;
	use codec::{Joiner, KeyedVec, Slicable};
	use keyring::Keyring::*;
	use primitives::hexdisplay::HexDisplay;
	use demo_primitives::{Header, Digest};
	use transaction::{UncheckedTransaction, Transaction};
	use runtime::staking;
	use dispatch::public::Call as PubCall;
	use runtime::staking::public::Call as StakingCall;

	#[test]
	fn staking_balance_transfer_dispatch_works() {
		let mut t: TestExternalities = map![
			twox_128(&staking::FreeBalanceOf::key_for(*One)).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(staking::TransactionFee::key()).to_vec() => vec![10u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(&BlockHashAt::key_for(&0)).to_vec() => [69u8; 32].encode()
		];

		let tx = UncheckedTransaction {
			transaction: Transaction {
				signed: One.into(),
				nonce: 0,
				function: PubCall::Staking(StakingCall::transfer(Two.into(), 69)),
			},
			signature: hex!("3a682213cb10e8e375fe0817fe4d220a4622d910088809ed7fc8b4ea3871531dbadb22acfedd28a100a0b7bd2d274e0ff873655b13c88f4640b5569db3222706").into(),
		};

		with_externalities(&mut t, || {
			internal::initialise_block(&Header::from_block_number(1));
			internal::execute_transaction(tx);
			assert_eq!(staking::balance(&One), 32);
			assert_eq!(staking::balance(&Two), 69);
		});
	}

	fn new_test_ext() -> TestExternalities {
		staking::testing::externalities(2, 2, 0)
	}

	#[test]
	fn block_import_works() {
		let mut t = new_test_ext();

		let h = Header {
			parent_hash: [69u8; 32].into(),
			number: 1,
			state_root: hex!("cc3f1f5db826013193e502c76992b5e933b12367e37a269a9822b89218323e9f").into(),
			transaction_root: hex!("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421").into(),
			digest: Digest { logs: vec![], },
		};

		let b = Block {
			header: h,
			transactions: vec![],
		};

		with_externalities(&mut t, || {
			execute_block(b);
		});
	}

	#[test]
	#[should_panic]
	fn block_import_of_bad_state_root_fails() {
		let mut t = new_test_ext();

		let h = Header {
			parent_hash: [69u8; 32].into(),
			number: 1,
			state_root: [0u8; 32].into(),
			transaction_root: hex!("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421").into(),
			digest: Digest { logs: vec![], },
		};

		let b = Block {
			header: h,
			transactions: vec![],
		};

		with_externalities(&mut t, || {
			execute_block(b);
		});
	}

	#[test]
	#[should_panic]
	fn block_import_of_bad_transaction_root_fails() {
		let mut t = new_test_ext();

		let h = Header {
			parent_hash: [69u8; 32].into(),
			number: 1,
			state_root: hex!("1ab2dbb7d4868a670b181327b0b6a58dc64b10cfb9876f737a5aa014b8da31e0").into(),
			transaction_root: [0u8; 32].into(),
			digest: Digest { logs: vec![], },
		};

		let b = Block {
			header: h,
			transactions: vec![],
		};

		with_externalities(&mut t, || {
			execute_block(b);
		});
	}
}
*/
