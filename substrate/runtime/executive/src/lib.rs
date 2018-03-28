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
#[cfg(test)] #[macro_use] extern crate serde_derive;
#[cfg(test)] extern crate substrate_primitives;
#[cfg(test)] extern crate substrate_runtime_consensus as consensus;
#[cfg(test)] extern crate substrate_runtime_session as session;
#[cfg(test)] extern crate substrate_runtime_staking as staking;

#[cfg(feature = "std")] extern crate serde;

use rstd::prelude::*;
use rstd::marker::PhantomData;
use runtime_io::Hashing;
use primitives::{Zero, One, Headery, Blocky, Checkable, Applyable, CheckEqual, Executable};
use codec::Slicable;

pub struct Executive<
	Unchecked,
	Checked,
	System,
	Block,
	Finalisation,
>(PhantomData<(Unchecked, Checked, System, Block, Finalisation)>);

impl<
	Unchecked: Checkable<
		Checked = Checked
	> + PartialEq + Eq + Clone + Slicable,
	Checked: Applyable<
		Index = System::Index,
		AccountId = System::AccountId
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

#[cfg(test)]
mod tests {
	use super::*;
	use staking::Call;
	use codec::{Slicable, Input};
	use runtime_io::with_externalities;
	use runtime_support::AuxDispatchable;
	use substrate_primitives::H256;
	use primitives::{Checkable, Applyable, HasPublicAux, Identity, Headery, Blocky, Digesty, MakeTestExternalities};

	#[derive(Default, PartialEq, Eq, Clone, Serialize, Debug)]
	pub struct Digest {
		pub logs: Vec<u64>,
	}
	impl Slicable for Digest {
		fn decode<I: Input>(input: &mut I) -> Option<Self> {
			Vec::<u64>::decode(input).map(|logs| Digest { logs })
		}
		fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
			self.logs.using_encoded(f)
		}
	}
	impl Digesty for Digest {
		type Item = u64;
		fn push(&mut self, item: Self::Item) {
			self.logs.push(item);
		}
	}

	#[derive(PartialEq, Eq, Clone, Serialize, Debug)]
	#[serde(rename_all = "camelCase")]
	#[serde(deny_unknown_fields)]
	pub struct Header {
		pub parent_hash: H256,
		pub number: u64,
		pub state_root: H256,
		pub extrinsics_root: H256,
		pub digest: Digest,
	}
	impl Slicable for Header {
		fn decode<I: Input>(input: &mut I) -> Option<Self> {
			Some(Header {
				parent_hash: Slicable::decode(input)?,
				number: Slicable::decode(input)?,
				state_root: Slicable::decode(input)?,
				extrinsics_root: Slicable::decode(input)?,
				digest: Slicable::decode(input)?,
			})
		}

		fn encode(&self) -> Vec<u8> {
			let mut v = Vec::new();
			self.parent_hash.using_encoded(|s| v.extend(s));
			self.number.using_encoded(|s| v.extend(s));
			self.state_root.using_encoded(|s| v.extend(s));
			self.extrinsics_root.using_encoded(|s| v.extend(s));
			self.digest.using_encoded(|s| v.extend(s));
			v
		}
	}
	impl Headery for Header {
		type Number = u64;
		type Hash = H256;
		type Digest = Digest;
		fn number(&self) -> &Self::Number { &self.number }
		fn extrinsics_root(&self) -> &Self::Hash { &self.extrinsics_root }
		fn state_root(&self) -> &Self::Hash { &self.state_root }
		fn parent_hash(&self) -> &Self::Hash { &self.parent_hash }
		fn digest(&self) -> &Self::Digest { &self.digest }
		fn new(
			number: Self::Number,
			extrinsics_root: Self::Hash,
			state_root: Self::Hash,
			parent_hash: Self::Hash,
			digest: Self::Digest
		) -> Self {
			Header {
				number, extrinsics_root: extrinsics_root, state_root, parent_hash, digest
			}
		}
	}

	#[derive(PartialEq, Eq, Clone, Serialize, Debug)]
	pub struct Block {
		pub header: Header,
		pub extrinsics: Vec<TestXt>,
	}
	impl Slicable for Block {
		fn decode<I: Input>(input: &mut I) -> Option<Self> {
			Some(Block {
				header: Slicable::decode(input)?,
				extrinsics: Slicable::decode(input)?,
			})
		}
		fn encode(&self) -> Vec<u8> {
			let mut v: Vec<u8> = Vec::new();
			v.extend(self.header.encode());
			v.extend(self.extrinsics.encode());
			v
		}
	}
	impl Blocky for Block {
		type Extrinsic = TestXt;
		type Header = Header;
		fn header(&self) -> &Self::Header {
			&self.header
		}
		fn extrinsics(&self) -> &[Self::Extrinsic] {
			&self.extrinsics[..]
		}
		fn deconstruct(self) -> (Self::Header, Vec<Self::Extrinsic>) {
			(self.header, self.extrinsics)
		}
	}

	pub struct Test;

	#[derive(PartialEq, Eq, Clone, Serialize, Debug)]
	pub struct TestXt((u64, u64, Call<Test>));
	impl Slicable for TestXt {
		fn decode<I: Input>(input: &mut I) -> Option<Self> {
			Some(TestXt(Slicable::decode(input)?))
		}
		fn encode(&self) -> Vec<u8> {
			self.0.encode()
		}
	}
	impl Checkable for TestXt {
		type Checked = Self;
		fn check(self) -> Result<Self, Self> { Ok(self) }
	}
	impl Applyable for TestXt {
		type AccountId = u64;
		type Index = u64;
		fn sender(&self) -> &u64 { &(self.0).0 }
		fn index(&self) -> &u64 { &(self.0).1 }
		fn apply(self) { <staking::Module<Test>>::make_payment(&(self.0).0); (self.0).2.dispatch(&(self.0).0) }
	}

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
	pub struct DummyContractAddressFor;
	impl staking::ContractAddressFor<u64> for DummyContractAddressFor {
		fn contract_address_for(_code: &[u8], origin: &u64) -> u64 {
			origin + 1
		}
	}
	impl staking::Trait for Test {
		type Balance = u64;
		type DetermineContractAddress = DummyContractAddressFor;
	}
	type Executive = super::Executive<TestXt, TestXt, Test, Block, ()>;

	#[test]
	fn staking_balance_transfer_dispatch_works() {
		let mut t = system::TestingConfig::<Test>::default().test_externalities();
		t.extend(staking::TestingConfig::<Test> {
			sessions_per_era: 0,
			current_era: 0,
			balances: vec![(1, 111)],
			intentions: vec![],
			validator_count: 0,
			bonding_duration: 0,
			transaction_fee: 10,
		}.test_externalities());
		let xt = TestXt((1, 0, Call::transfer(2, 69)));
		with_externalities(&mut t, || {
			Executive::initialise_block(&Header::new(1, H256::default(), H256::default(), [69u8; 32].into(), Digest::default()));
			Executive::apply_extrinsic(xt);
			assert_eq!(<staking::Module<Test>>::balance(&1), 32);
			assert_eq!(<staking::Module<Test>>::balance(&2), 69);
		});
	}

/*
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
*/
}
