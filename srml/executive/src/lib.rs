// Copyright 2017-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! # Executive Module
//!
//! The Executive module acts as the orchestration layer for the runtime. It dispatches incoming
//! extrinsic calls to the respective modules in the runtime.
//!
//! ## Overview
//!
//! The executive module is not a typical SRML module providing functionality around a specific feature.
//! It is a cross-cutting framework component for the SRML. It works in conjunction with the
//! [SRML System module](../srml_system/index.html) to perform these cross-cutting functions.
//!
//! The Executive module provides functions to:
//!
//! - Check transaction validity.
//! - Initialize a block.
//! - Apply extrinsics.
//! - Execute a block.
//! - Finalize a block.
//! - Start an off-chain worker.
//!
//! ### Implementations
//!
//! The Executive module provides the following implementations:
//!
//! - `ExecuteBlock`: Trait that can be used to execute a block.
//! - `Executive`: Type that can be used to make the SRML available from the runtime.
//!
//! ## Usage
//!
//! The default Substrate node template declares the [`Executive`](./struct.Executive.html) type in its library.
//!
//! ### Example
//!
//! `Executive` type declaration from the node template.
//!
//! ```
//! # use sr_primitives::generic;
//! # use srml_executive as executive;
//! # pub struct UncheckedExtrinsic {};
//! # pub struct Header {};
//! # type Context = system::ChainContext<Runtime>;
//! # pub type Block = generic::Block<Header, UncheckedExtrinsic>;
//! # pub type Balances = u64;
//! # pub type AllModules = u64;
//! # pub enum Runtime {};
//! # use sr_primitives::transaction_validity::TransactionValidity;
//! # use sr_primitives::traits::ValidateUnsigned;
//! # impl ValidateUnsigned for Runtime {
//! # 	type Call = ();
//! #
//! # 	fn validate_unsigned(_call: &Self::Call) -> TransactionValidity {
//! # 		TransactionValidity::Invalid(0)
//! # 	}
//! # }
//! /// Executive: handles dispatch to the various modules.
//! pub type Executive = executive::Executive<Runtime, Block, Context, Runtime, AllModules>;
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

use rstd::prelude::*;
use rstd::marker::PhantomData;
use rstd::result;
use sr_primitives::{generic::Digest, traits::{
	self, Header, Zero, One, Checkable, Applyable, CheckEqual, OnFinalize,
	OnInitialize, NumberFor, Block as BlockT, OffchainWorker, ValidateUnsigned
}};
use srml_support::Dispatchable;
use codec::{Codec, Encode};
use system::{extrinsics_root, DigestOf};
use sr_primitives::{ApplyOutcome, ApplyError};
use sr_primitives::transaction_validity::TransactionValidity;
use sr_primitives::weights::GetDispatchInfo;

mod internal {
	use sr_primitives::traits::DispatchError;

	pub enum ApplyError {
		BadSignature(&'static str),
		Stale,
		Future,
		CantPay,
		FullBlock,
	}

	pub enum ApplyOutcome {
		Success,
		Fail(&'static str),
	}

	impl From<DispatchError> for ApplyError {
		fn from(d: DispatchError) -> Self {
			match d {
				DispatchError::Payment => ApplyError::CantPay,
				DispatchError::Exhausted => ApplyError::FullBlock,
				DispatchError::NoPermission => ApplyError::CantPay,
				DispatchError::BadState => ApplyError::CantPay,
				DispatchError::Stale => ApplyError::Stale,
				DispatchError::Future => ApplyError::Future,
				DispatchError::BadProof => ApplyError::BadSignature(""),
			}
		}
	}
}

/// Trait that can be used to execute a block.
pub trait ExecuteBlock<Block: BlockT> {
	/// Actually execute all transitions for `block`.
	fn execute_block(block: Block);
}

pub type CheckedOf<E, C> = <E as Checkable<C>>::Checked;
pub type CallOf<E, C> = <CheckedOf<E, C> as Applyable>::Call;
pub type OriginOf<E, C> = <CallOf<E, C> as Dispatchable>::Origin;

pub struct Executive<System, Block, Context, UnsignedValidator, AllModules>(
	PhantomData<(System, Block, Context, UnsignedValidator, AllModules)>
);

impl<
	System: system::Trait,
	Block: traits::Block<Header=System::Header, Hash=System::Hash>,
	Context: Default,
	UnsignedValidator,
	AllModules: OnInitialize<System::BlockNumber> + OnFinalize<System::BlockNumber> + OffchainWorker<System::BlockNumber>,
> ExecuteBlock<Block> for Executive<System, Block, Context, UnsignedValidator, AllModules>
where
	Block::Extrinsic: Checkable<Context> + Codec,
	CheckedOf<Block::Extrinsic, Context>: Applyable<AccountId=System::AccountId> + GetDispatchInfo,
	CallOf<Block::Extrinsic, Context>: Dispatchable,
	OriginOf<Block::Extrinsic, Context>: From<Option<System::AccountId>>,
	UnsignedValidator: ValidateUnsigned<Call=CallOf<Block::Extrinsic, Context>>,
{
	fn execute_block(block: Block) {
		Executive::<System, Block, Context, UnsignedValidator, AllModules>::execute_block(block);
	}
}

impl<
	System: system::Trait,
	Block: traits::Block<Header=System::Header, Hash=System::Hash>,
	Context: Default,
	UnsignedValidator,
	AllModules: OnInitialize<System::BlockNumber> + OnFinalize<System::BlockNumber> + OffchainWorker<System::BlockNumber>,
> Executive<System, Block, Context, UnsignedValidator, AllModules>
where
	Block::Extrinsic: Checkable<Context> + Codec,
	CheckedOf<Block::Extrinsic, Context>: Applyable<AccountId=System::AccountId> + GetDispatchInfo,
	CallOf<Block::Extrinsic, Context>: Dispatchable,
	OriginOf<Block::Extrinsic, Context>: From<Option<System::AccountId>>,
	UnsignedValidator: ValidateUnsigned<Call=CallOf<Block::Extrinsic, Context>>,
{
	/// Start the execution of a particular block.
	pub fn initialize_block(header: &System::Header) {
		let mut digests = <DigestOf<System>>::default();
		header.digest().logs().iter().for_each(|d| if d.as_pre_runtime().is_some() { digests.push(d.clone()) });
		Self::initialize_block_impl(header.number(), header.parent_hash(), header.extrinsics_root(), &digests);
	}

	fn initialize_block_impl(
		block_number: &System::BlockNumber,
		parent_hash: &System::Hash,
		extrinsics_root: &System::Hash,
		digest: &Digest<System::Hash>,
	) {
		<system::Module<System>>::initialize(block_number, parent_hash, extrinsics_root, digest);
		<AllModules as OnInitialize<System::BlockNumber>>::on_initialize(*block_number);
	}

	fn initial_checks(block: &Block) {
		let header = block.header();

		// Check that `parent_hash` is correct.
		let n = header.number().clone();
		assert!(
			n > System::BlockNumber::zero()
			&& <system::Module<System>>::block_hash(n - System::BlockNumber::one()) == *header.parent_hash(),
			"Parent hash should be valid."
		);

		// Check that transaction trie root represents the transactions.
		let xts_root = extrinsics_root::<System::Hashing, _>(&block.extrinsics());
		header.extrinsics_root().check_equal(&xts_root);
		assert!(header.extrinsics_root() == &xts_root, "Transaction trie root must be valid.");
	}

	/// Actually execute all transitions for `block`.
	pub fn execute_block(block: Block) {
		Self::initialize_block(block.header());

		// any initial checks
		Self::initial_checks(&block);

		// execute extrinsics
		let (header, extrinsics) = block.deconstruct();
		Self::execute_extrinsics_with_book_keeping(extrinsics, *header.number());

		// any final checks
		Self::final_checks(&header);
	}

	/// Execute given extrinsics and take care of post-extrinsics book-keeping.
	fn execute_extrinsics_with_book_keeping(extrinsics: Vec<Block::Extrinsic>, block_number: NumberFor<Block>) {

		extrinsics.into_iter().for_each(Self::apply_extrinsic_no_note);

		// post-extrinsics book-keeping
		<system::Module<System>>::note_finished_extrinsics();
		<AllModules as OnFinalize<System::BlockNumber>>::on_finalize(block_number);
	}

	/// Finalize the block - it is up the caller to ensure that all header fields are valid
	/// except state-root.
	pub fn finalize_block() -> System::Header {
		<system::Module<System>>::note_finished_extrinsics();
		<AllModules as OnFinalize<System::BlockNumber>>::on_finalize(<system::Module<System>>::block_number());

		// set up extrinsics
		<system::Module<System>>::derive_extrinsics();
		<system::Module<System>>::finalize()
	}

	/// Apply extrinsic outside of the block execution function.
	/// This doesn't attempt to validate anything regarding the block, but it builds a list of uxt
	/// hashes.
	pub fn apply_extrinsic(uxt: Block::Extrinsic) -> result::Result<ApplyOutcome, ApplyError> {
		let encoded = uxt.encode();
		let encoded_len = encoded.len();
		match Self::apply_extrinsic_with_len(uxt, encoded_len, Some(encoded)) {
			Ok(internal::ApplyOutcome::Success) => Ok(ApplyOutcome::Success),
			Ok(internal::ApplyOutcome::Fail(_)) => Ok(ApplyOutcome::Fail),
			Err(internal::ApplyError::CantPay) => Err(ApplyError::CantPay),
			Err(internal::ApplyError::BadSignature(_)) => Err(ApplyError::BadSignature),
			Err(internal::ApplyError::Stale) => Err(ApplyError::Stale),
			Err(internal::ApplyError::Future) => Err(ApplyError::Future),
			Err(internal::ApplyError::FullBlock) => Err(ApplyError::FullBlock),
		}
	}

	/// Apply an extrinsic inside the block execution function.
	fn apply_extrinsic_no_note(uxt: Block::Extrinsic) {
		let l = uxt.encode().len();
		match Self::apply_extrinsic_with_len(uxt, l, None) {
			Ok(internal::ApplyOutcome::Success) => (),
			Ok(internal::ApplyOutcome::Fail(e)) => runtime_io::print(e),
			Err(internal::ApplyError::CantPay) => panic!("All extrinsics should have sender able to pay their fees"),
			Err(internal::ApplyError::BadSignature(_)) => panic!("All extrinsics should be properly signed"),
			Err(internal::ApplyError::Stale) | Err(internal::ApplyError::Future) => panic!("All extrinsics should have the correct nonce"),
			Err(internal::ApplyError::FullBlock) => panic!("Extrinsics should not exceed block limit"),
		}
	}

	/// Actually apply an extrinsic given its `encoded_len`; this doesn't note its hash.
	fn apply_extrinsic_with_len(
		uxt: Block::Extrinsic,
		encoded_len: usize,
		to_note: Option<Vec<u8>>,
	) -> result::Result<internal::ApplyOutcome, internal::ApplyError> {
		// Verify that the signature is good.
		let xt = uxt.check(&Default::default()).map_err(internal::ApplyError::BadSignature)?;

		// We don't need to make sure to `note_extrinsic` only after we know it's going to be
		// executed to prevent it from leaking in storage since at this point, it will either
		// execute or panic (and revert storage changes).
		if let Some(encoded) = to_note {
			<system::Module<System>>::note_extrinsic(encoded);
		}

		// AUDIT: Under no circumstances may this function panic from here onwards.

		// Decode parameters and dispatch
		let dispatch_info = xt.get_dispatch_info();
		let r = Applyable::dispatch(xt, dispatch_info, encoded_len)
			.map_err(internal::ApplyError::from)?;

		<system::Module<System>>::note_applied_extrinsic(&r, encoded_len as u32);

		r.map(|_| internal::ApplyOutcome::Success).or_else(|e| match e {
			sr_primitives::BLOCK_FULL => Err(internal::ApplyError::FullBlock),
			e => Ok(internal::ApplyOutcome::Fail(e))
		})
	}

	fn final_checks(header: &System::Header) {
		// remove temporaries
		let new_header = <system::Module<System>>::finalize();

		// check digest
		assert_eq!(
			header.digest().logs().len(),
			new_header.digest().logs().len(),
			"Number of digest items must match that calculated."
		);
		let items_zip = header.digest().logs().iter().zip(new_header.digest().logs().iter());
		for (header_item, computed_item) in items_zip {
			header_item.check_equal(&computed_item);
			assert!(header_item == computed_item, "Digest item must match that calculated.");
		}

		// check storage root.
		let storage_root = new_header.state_root();
		header.state_root().check_equal(&storage_root);
		assert!(header.state_root() == storage_root, "Storage root must match that calculated.");
	}

	/// Check a given signed transaction for validity. This doesn't execute any
	/// side-effects; it merely checks whether the transaction would panic if it were included or not.
	///
	/// Changes made to storage should be discarded.
	pub fn validate_transaction(uxt: Block::Extrinsic) -> TransactionValidity {
		// Note errors > 0 are from ApplyError
		const UNKNOWN_ERROR: i8 = -127;
		const INVALID_INDEX: i8 = -10;

		let encoded_len = uxt.using_encoded(|d| d.len());
		let xt = match uxt.check(&Default::default()) {
			// Checks out. Carry on.
			Ok(xt) => xt,
			// An unknown account index implies that the transaction may yet become valid.
			Err("invalid account index") => return TransactionValidity::Unknown(INVALID_INDEX),
			// Technically a bad signature could also imply an out-of-date account index, but
			// that's more of an edge case.
			Err(sr_primitives::BAD_SIGNATURE) => return TransactionValidity::Invalid(ApplyError::BadSignature as i8),
			Err(_) => return TransactionValidity::Invalid(UNKNOWN_ERROR),
		};

		let dispatch_info = xt.get_dispatch_info();
		xt.validate::<UnsignedValidator>(dispatch_info, encoded_len)
	}

	/// Start an offchain worker and generate extrinsics.
	pub fn offchain_worker(n: System::BlockNumber) {
		<AllModules as OffchainWorker<System::BlockNumber>>::generate_extrinsics(n)
	}
}


#[cfg(test)]
mod tests {
	use super::*;
	use balances::Call;
	use runtime_io::with_externalities;
	use primitives::{H256, Blake2Hasher};
	use sr_primitives::generic::Era;
	use sr_primitives::Perbill;
	use sr_primitives::weights::Weight;
	use sr_primitives::traits::{Header as HeaderT, BlakeTwo256, IdentityLookup, ConvertInto};
	use sr_primitives::testing::{Digest, Header, Block};
	use srml_support::{impl_outer_event, impl_outer_origin, parameter_types};
	use srml_support::traits::{Currency, LockIdentifier, LockableCurrency, WithdrawReasons, WithdrawReason};
	use system;
	use hex_literal::hex;

	impl_outer_origin! {
		pub enum Origin for Runtime { }
	}

	impl_outer_event!{
		pub enum MetaEvent for Runtime {
			balances<T>,
		}
	}

	// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
	#[derive(Clone, Eq, PartialEq)]
	pub struct Runtime;
	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: u32 = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
	}
	impl system::Trait for Runtime {
		type Origin = Origin;
		type Index = u64;
		type Call = Call<Runtime>;
		type BlockNumber = u64;
		type Hash = primitives::H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<u64>;
		type Header = Header;
		type Event = MetaEvent;
		type BlockHashCount = BlockHashCount;
		type WeightMultiplierUpdate = ();
		type MaximumBlockWeight = MaximumBlockWeight;
		type AvailableBlockRatio = AvailableBlockRatio;
		type MaximumBlockLength = MaximumBlockLength;
		type Version = ();
	}
	parameter_types! {
		pub const ExistentialDeposit: u64 = 0;
		pub const TransferFee: u64 = 0;
		pub const CreationFee: u64 = 0;
		pub const TransactionBaseFee: u64 = 10;
		pub const TransactionByteFee: u64 = 0;
	}
	impl balances::Trait for Runtime {
		type Balance = u64;
		type OnFreeBalanceZero = ();
		type OnNewAccount = ();
		type Event = MetaEvent;
		type TransactionPayment = ();
		type DustRemoval = ();
		type TransferPayment = ();
		type ExistentialDeposit = ExistentialDeposit;
		type TransferFee = TransferFee;
		type CreationFee = CreationFee;
		type TransactionBaseFee = TransactionBaseFee;
		type TransactionByteFee = TransactionByteFee;
		type WeightToFee = ConvertInto;
	}

	impl ValidateUnsigned for Runtime {
		type Call = Call<Runtime>;

		fn validate_unsigned(call: &Self::Call) -> TransactionValidity {
			match call {
				Call::set_balance(_, _, _) => TransactionValidity::Valid(Default::default()),
				_ => TransactionValidity::Invalid(0),
			}
		}
	}

	type SignedExtra = (
		system::CheckEra<Runtime>,
		system::CheckNonce<Runtime>,
		system::CheckWeight<Runtime>,
		balances::TakeFees<Runtime>
	);
	type TestXt = sr_primitives::testing::TestXt<Call<Runtime>, SignedExtra>;
	type Executive = super::Executive<Runtime, Block<TestXt>, system::ChainContext<Runtime>, Runtime, ()>;

	fn extra(nonce: u64, fee: u64) -> SignedExtra {
		(
			system::CheckEra::from(Era::Immortal),
			system::CheckNonce::from(nonce),
			system::CheckWeight::new(),
			balances::TakeFees::from(fee)
		)
	}

	fn sign_extra(who: u64, nonce: u64, fee: u64) -> Option<(u64, SignedExtra)> {
		Some((who, extra(nonce, fee)))
	}

	#[test]
	fn balance_transfer_dispatch_works() {
		let mut t = system::GenesisConfig::default().build_storage::<Runtime>().unwrap();
		balances::GenesisConfig::<Runtime> {
			balances: vec![(1, 211)],
			vesting: vec![],
		}.assimilate_storage(&mut t).unwrap();
		let xt = sr_primitives::testing::TestXt(sign_extra(1, 0, 0), Call::transfer(2, 69));
		let weight = xt.get_dispatch_info().weight as u64;
		let mut t = runtime_io::TestExternalities::<Blake2Hasher>::new(t);
		with_externalities(&mut t, || {
			Executive::initialize_block(&Header::new(
				1,
				H256::default(),
				H256::default(),
				[69u8; 32].into(),
				Digest::default(),
			));
			let r = Executive::apply_extrinsic(xt);
			assert_eq!(r, Ok(ApplyOutcome::Success));
			assert_eq!(<balances::Module<Runtime>>::total_balance(&1), 142 - 10 - weight);
			assert_eq!(<balances::Module<Runtime>>::total_balance(&2), 69);
		});
	}

	fn new_test_ext(balance_factor: u64) -> runtime_io::TestExternalities<Blake2Hasher> {
		let mut t = system::GenesisConfig::default().build_storage::<Runtime>().unwrap();
		balances::GenesisConfig::<Runtime> {
			balances: vec![(1, 111 * balance_factor)],
			vesting: vec![],
		}.assimilate_storage(&mut t).unwrap();
		t.into()
	}

	#[test]
	fn block_import_works() {
		with_externalities(&mut new_test_ext(1), || {
			Executive::execute_block(Block {
				header: Header {
					parent_hash: [69u8; 32].into(),
					number: 1,
					state_root: hex!("3e51b47b6cc8449eece93eee4b01f03b00a0ca7981c0b6c0447b6e0d50ca886d").into(),
					extrinsics_root: hex!("03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314").into(),
					digest: Digest { logs: vec![], },
				},
				extrinsics: vec![],
			});
		});
	}

	#[test]
	#[should_panic]
	fn block_import_of_bad_state_root_fails() {
		with_externalities(&mut new_test_ext(1), || {
			Executive::execute_block(Block {
				header: Header {
					parent_hash: [69u8; 32].into(),
					number: 1,
					state_root: [0u8; 32].into(),
					extrinsics_root: hex!("03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314").into(),
					digest: Digest { logs: vec![], },
				},
				extrinsics: vec![],
			});
		});
	}

	#[test]
	#[should_panic]
	fn block_import_of_bad_extrinsic_root_fails() {
		with_externalities(&mut new_test_ext(1), || {
			Executive::execute_block(Block {
				header: Header {
					parent_hash: [69u8; 32].into(),
					number: 1,
					state_root: hex!("49cd58a254ccf6abc4a023d9a22dcfc421e385527a250faec69f8ad0d8ed3e48").into(),
					extrinsics_root: [0u8; 32].into(),
					digest: Digest { logs: vec![], },
				},
				extrinsics: vec![],
			});
		});
	}

	#[test]
	fn bad_extrinsic_not_inserted() {
		let mut t = new_test_ext(1);
		// bad nonce check!
		let xt = sr_primitives::testing::TestXt(sign_extra(1, 30, 0), Call::transfer(33, 69));
		with_externalities(&mut t, || {
			Executive::initialize_block(&Header::new(
				1,
				H256::default(),
				H256::default(),
				[69u8; 32].into(),
				Digest::default(),
			));
			assert!(Executive::apply_extrinsic(xt).is_err());
			assert_eq!(<system::Module<Runtime>>::extrinsic_index(), Some(0));
		});
	}

	#[test]
	fn block_weight_limit_enforced() {
		let mut t = new_test_ext(10000);
		// given: TestXt uses the encoded len as fixed Len:
		let xt = sr_primitives::testing::TestXt(sign_extra(1, 0, 0), Call::transfer::<Runtime>(33, 0));
		let encoded = xt.encode();
		let encoded_len = encoded.len() as Weight;
		let limit = AvailableBlockRatio::get() * MaximumBlockWeight::get();
		let num_to_exhaust_block = limit / encoded_len;
		with_externalities(&mut t, || {
			Executive::initialize_block(&Header::new(
				1,
				H256::default(),
				H256::default(),
				[69u8; 32].into(),
				Digest::default(),
			));
			assert_eq!(<system::Module<Runtime>>::all_extrinsics_weight(), 0);

			for nonce in 0..=num_to_exhaust_block {
				let xt = sr_primitives::testing::TestXt(sign_extra(1, nonce.into(), 0), Call::transfer::<Runtime>(33, 0));
				let res = Executive::apply_extrinsic(xt);
				if nonce != num_to_exhaust_block {
					assert_eq!(res.unwrap(), ApplyOutcome::Success);
					assert_eq!(<system::Module<Runtime>>::all_extrinsics_weight(), encoded_len * (nonce + 1));
					assert_eq!(<system::Module<Runtime>>::extrinsic_index(), Some(nonce as u32 + 1));
				} else {
					assert_eq!(res, Err(ApplyError::FullBlock));
				}
			}
		});
	}

	#[test]
	fn block_weight_and_size_is_stored_per_tx() {
		let xt = sr_primitives::testing::TestXt(sign_extra(1, 0, 0), Call::transfer(33, 0));
		let x1 = sr_primitives::testing::TestXt(sign_extra(1, 1, 0), Call::transfer(33, 0));
		let x2 = sr_primitives::testing::TestXt(sign_extra(1, 2, 0), Call::transfer(33, 0));
		let len = xt.clone().encode().len() as u32;
		let mut t = new_test_ext(1);
		with_externalities(&mut t, || {
			assert_eq!(<system::Module<Runtime>>::all_extrinsics_weight(), 0);
			assert_eq!(<system::Module<Runtime>>::all_extrinsics_weight(), 0);

			assert_eq!(Executive::apply_extrinsic(xt.clone()).unwrap(), ApplyOutcome::Success);
			assert_eq!(Executive::apply_extrinsic(x1.clone()).unwrap(), ApplyOutcome::Success);
			assert_eq!(Executive::apply_extrinsic(x2.clone()).unwrap(), ApplyOutcome::Success);

			// default weight for `TestXt` == encoded length.
			assert_eq!(<system::Module<Runtime>>::all_extrinsics_weight(), (3 * len).into());
			assert_eq!(<system::Module<Runtime>>::all_extrinsics_len(), 3 * len);

			let _ = <system::Module<Runtime>>::finalize();

			assert_eq!(<system::Module<Runtime>>::all_extrinsics_weight(), 0);
			assert_eq!(<system::Module<Runtime>>::all_extrinsics_weight(), 0);
		});
	}

	#[test]
	fn validate_unsigned() {
		let xt = sr_primitives::testing::TestXt(None, Call::set_balance(33, 69, 69));
		let valid = TransactionValidity::Valid(Default::default());
		let mut t = new_test_ext(1);

		with_externalities(&mut t, || {
			assert_eq!(Executive::validate_transaction(xt.clone()), valid);
			assert_eq!(Executive::apply_extrinsic(xt), Ok(ApplyOutcome::Fail));
		});
	}

	#[test]
	fn can_pay_for_tx_fee_on_full_lock() {
		let id: LockIdentifier = *b"0       ";
		let execute_with_lock = |lock: WithdrawReasons| {
			let mut t = new_test_ext(1);
			with_externalities(&mut t, || {
				<balances::Module<Runtime> as LockableCurrency<u64>>::set_lock(
					id,
					&1,
					110,
					10,
					lock,
				);
				let xt = sr_primitives::testing::TestXt(sign_extra(1, 0, 0), Call::transfer(2, 10));
				let weight = xt.get_dispatch_info().weight as u64;
				Executive::initialize_block(&Header::new(
					1,
					H256::default(),
					H256::default(),
					[69u8; 32].into(),
					Digest::default(),
				));

				if lock == WithdrawReasons::except(WithdrawReason::TransactionPayment) {
					assert_eq!(Executive::apply_extrinsic(xt).unwrap(), ApplyOutcome::Fail);
					// but tx fee has been deducted. the transaction failed on transfer, not on fee.
					assert_eq!(<balances::Module<Runtime>>::total_balance(&1), 111 - 10 - weight);
				} else {
					assert_eq!(Executive::apply_extrinsic(xt), Err(ApplyError::CantPay));
					assert_eq!(<balances::Module<Runtime>>::total_balance(&1), 111);
				}
			});
		};

		execute_with_lock(WithdrawReasons::all());
		execute_with_lock(WithdrawReasons::except(WithdrawReason::TransactionPayment));
	}
}
