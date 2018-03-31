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

//! Executive: Handles all of the top-level stuff; essentially just executing blocks/extrinsics.

#![cfg_attr(not(feature = "std"), no_std)]

extern crate substrate_runtime_std as rstd;
extern crate substrate_runtime_support as runtime_support;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_codec as codec;
extern crate substrate_runtime_primitives as primitives;
extern crate substrate_runtime_system as system;
#[cfg(test)] #[macro_use] extern crate hex_literal;
#[cfg(test)] extern crate substrate_primitives;
#[cfg(test)] extern crate substrate_runtime_consensus as consensus;
#[cfg(test)] extern crate substrate_runtime_session as session;
#[cfg(test)] extern crate substrate_runtime_staking as staking;

#[cfg(feature = "std")] extern crate serde;

use rstd::prelude::*;
use rstd::marker::PhantomData;
use runtime_io::Hashing;
use primitives::traits::{self, Headery, Zero, One, Checkable, Applyable, CheckEqual, Executable, MakePayment};
use codec::Slicable;

pub struct Executive<
	System,
	Block,
	Payment,
	Finalisation,
>(PhantomData<(System, Block, Payment, Finalisation)>);

impl<
	System: system::Trait,
	Block: traits::Blocky<Header = System::Header>,
	Payment: MakePayment<System::AccountId>,
	Finalisation: Executable,
> Executive<System, Block, Payment, Finalisation> where
	Block::Extrinsic: Checkable + Slicable,
	<Block::Extrinsic as Checkable>::Checked: Applyable<Index = System::Index, AccountId = System::AccountId>
{
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
	pub fn apply_extrinsic(utx: Block::Extrinsic) {
		// Verify the signature is good.
		let tx = match utx.check() {
			Ok(tx) => tx,
			Err(_) => panic!("All transactions should be properly signed"),
		};

		{
			// check index
			let expected_index = <system::Module<System>>::account_index(tx.sender());
			assert!(tx.index() == &expected_index, "All transactions should have the correct nonce");

			// increment nonce in storage
			<system::Module<System>>::inc_account_index(tx.sender());
		}

		// pay any fees.
		Payment::make_payment(tx.sender());

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

#[cfg(test)]
mod tests {
	use super::*;
	use staking::Call;
	use runtime_io::with_externalities;
	use substrate_primitives::H256;
	use primitives::BuildExternalities;
	use primitives::traits::{self, HasPublicAux, Identity};
	use primitives::testing::{Digest, Header, Block};

	pub struct Test;
	impl HasPublicAux for Test {
		type PublicAux = u64;
	}
	impl consensus::Trait for Test {
		type SessionKey = u64;
	}
	impl system::Trait for Test {
		type Index = u64;
		type BlockNumber = u64;
		type Hash = substrate_primitives::H256;
		type Hashing = runtime_io::BlakeTwo256;
		type Digest = Digest;
		type AccountId = u64;
		type Header = Header;
	}
	impl session::Trait for Test {
		type PublicAux = <Self as HasPublicAux>::PublicAux;
		type ConvertAccountIdToSessionKey = Identity;
	}
	impl staking::Trait for Test {
		type Balance = u64;
		type DetermineContractAddress = staking::DummyContractAddressFor;
	}

	type TestXt = primitives::testing::TestXt<Call<Test>>;
	type Executive = super::Executive<Test, Block<TestXt>, staking::Module<Test>, (session::Module<Test>, staking::Module<Test>)>;

	#[test]
	fn staking_balance_transfer_dispatch_works() {
		let mut t = system::GenesisConfig::<Test>::default().build_externalities();
		t.extend(staking::GenesisConfig::<Test> {
			sessions_per_era: 0,
			current_era: 0,
			balances: vec![(1, 111)],
			intentions: vec![],
			validator_count: 0,
			bonding_duration: 0,
			transaction_fee: 10,
		}.build_externalities());
		let xt = primitives::testing::TestXt((1, 0, Call::transfer(2, 69)));
		with_externalities(&mut t, || {
			Executive::initialise_block(&Header::new(1, H256::default(), H256::default(), [69u8; 32].into(), Digest::default()));
			Executive::apply_extrinsic(xt);
			assert_eq!(<staking::Module<Test>>::balance(&1), 32);
			assert_eq!(<staking::Module<Test>>::balance(&2), 69);
		});
	}

	fn new_test_ext() -> runtime_io::TestExternalities {
		let mut t = system::GenesisConfig::<Test>::default().build_externalities();
		t.extend(consensus::GenesisConfig::<Test>::default().build_externalities());
		t.extend(session::GenesisConfig::<Test>::default().build_externalities());
		t.extend(staking::GenesisConfig::<Test>::default().build_externalities());
		t
	}

	#[test]
	fn block_import_works() {
		with_externalities(&mut new_test_ext(), || {
			Executive::execute_block(Block {
				header: Header {
					parent_hash: [69u8; 32].into(),
					number: 1,
					state_root: hex!("9228e363883f4f5a01981985b5598d1a767e987eb3ccea017a0e14cac7acc79d").into(),
					extrinsics_root: hex!("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421").into(),
					digest: Digest { logs: vec![], },
				},
				extrinsics: vec![],
			});
		});
	}

	#[test]
	#[should_panic]
	fn block_import_of_bad_state_root_fails() {
		with_externalities(&mut new_test_ext(), || {
			Executive::execute_block(Block {
				header: Header {
					parent_hash: [69u8; 32].into(),
					number: 1,
					state_root: [0u8; 32].into(),
					extrinsics_root: hex!("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421").into(),
					digest: Digest { logs: vec![], },
				},
				extrinsics: vec![],
			});
		});
	}

	#[test]
	#[should_panic]
	fn block_import_of_bad_extrinsic_root_fails() {
		with_externalities(&mut new_test_ext(), || {
			Executive::execute_block(Block {
				header: Header {
					parent_hash: [69u8; 32].into(),
					number: 1,
					state_root: hex!("93dde1251278e65430baf291337ba219bacfa9ad583c52513b12cf1974109a97").into(),
					extrinsics_root: [0u8; 32].into(),
					digest: Digest { logs: vec![], },
				},
				extrinsics: vec![],
			});
		});
	}
}
