// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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
//! [SRML System module](../frame_system/index.html) to perform these cross-cutting functions.
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
//! # use sp_runtime::generic;
//! # use frame_executive as executive;
//! # pub struct UncheckedExtrinsic {};
//! # pub struct Header {};
//! # type Context = frame_system::ChainContext<Runtime>;
//! # pub type Block = generic::Block<Header, UncheckedExtrinsic>;
//! # pub type Balances = u64;
//! # pub type AllModules = u64;
//! # pub enum Runtime {};
//! # use sp_runtime::transaction_validity::{TransactionValidity, UnknownTransaction};
//!	# #[allow(deprecated)]
//! # use sp_runtime::traits::ValidateUnsigned;
//!	# #[allow(deprecated)]
//! # impl ValidateUnsigned for Runtime {
//! # 	type Call = ();
//! #
//! # 	fn validate_unsigned(_call: &Self::Call) -> TransactionValidity {
//! # 		UnknownTransaction::NoUnsignedValidator.into()
//! # 	}
//! # }
//! /// Executive: handles dispatch to the various modules.
//! pub type Executive = executive::Executive<Runtime, Block, Context, Runtime, AllModules>;
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::{prelude::*, marker::PhantomData};
use frame_support::weights::{GetDispatchInfo, WeighBlock, DispatchInfo};
use sp_runtime::{
	generic::Digest, ApplyExtrinsicResult,
	traits::{
		self, Header, Zero, One, Checkable, Applyable, CheckEqual, OnFinalize, OnInitialize,
		NumberFor, Block as BlockT, OffchainWorker, Dispatchable, Saturating,
	},
	transaction_validity::TransactionValidity,
};
#[allow(deprecated)]
use sp_runtime::traits::ValidateUnsigned;
use codec::{Codec, Encode};
use frame_system::{extrinsics_root, DigestOf};

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

#[allow(deprecated)] // Allow ValidateUnsigned, remove the attribute when the trait is removed.
impl<
	System: frame_system::Trait,
	Block: traits::Block<Header=System::Header, Hash=System::Hash>,
	Context: Default,
	UnsignedValidator,
	AllModules:
		OnInitialize<System::BlockNumber> +
		OnFinalize<System::BlockNumber> +
		OffchainWorker<System::BlockNumber> +
		WeighBlock<System::BlockNumber>,
> ExecuteBlock<Block> for Executive<System, Block, Context, UnsignedValidator, AllModules>
where
	Block::Extrinsic: Checkable<Context> + Codec,
	CheckedOf<Block::Extrinsic, Context>:
		Applyable<AccountId=System::AccountId, DispatchInfo=DispatchInfo> +
		GetDispatchInfo,
	CallOf<Block::Extrinsic, Context>: Dispatchable,
	OriginOf<Block::Extrinsic, Context>: From<Option<System::AccountId>>,
	UnsignedValidator: ValidateUnsigned<Call=CallOf<Block::Extrinsic, Context>>,
{
	fn execute_block(block: Block) {
		Executive::<System, Block, Context, UnsignedValidator, AllModules>::execute_block(block);
	}
}

#[allow(deprecated)] // Allow ValidateUnsigned, remove the attribute when the trait is removed.
impl<
	System: frame_system::Trait,
	Block: traits::Block<Header=System::Header, Hash=System::Hash>,
	Context: Default,
	UnsignedValidator,
	AllModules:
		OnInitialize<System::BlockNumber> +
		OnFinalize<System::BlockNumber> +
		OffchainWorker<System::BlockNumber> +
		WeighBlock<System::BlockNumber>,
> Executive<System, Block, Context, UnsignedValidator, AllModules>
where
	Block::Extrinsic: Checkable<Context> + Codec,
	CheckedOf<Block::Extrinsic, Context>:
		Applyable<AccountId=System::AccountId, DispatchInfo=DispatchInfo> +
		GetDispatchInfo,
	CallOf<Block::Extrinsic, Context>: Dispatchable,
	OriginOf<Block::Extrinsic, Context>: From<Option<System::AccountId>>,
	UnsignedValidator: ValidateUnsigned<Call=CallOf<Block::Extrinsic, Context>>,
{
	/// Start the execution of a particular block.
	pub fn initialize_block(header: &System::Header) {
		let digests = Self::extract_pre_digest(&header);
		Self::initialize_block_impl(
			header.number(),
			header.parent_hash(),
			header.extrinsics_root(),
			&digests
		);
	}

	fn extract_pre_digest(header: &System::Header) -> DigestOf<System> {
		let mut digest = <DigestOf<System>>::default();
		header.digest().logs()
			.iter()
			.for_each(|d| if d.as_pre_runtime().is_some() {
				digest.push(d.clone())
			});
		digest
	}

	fn initialize_block_impl(
		block_number: &System::BlockNumber,
		parent_hash: &System::Hash,
		extrinsics_root: &System::Hash,
		digest: &Digest<System::Hash>,
	) {
		<frame_system::Module<System>>::initialize(
			block_number,
			parent_hash,
			extrinsics_root,
			digest,
			frame_system::InitKind::Full,
		);
		<AllModules as OnInitialize<System::BlockNumber>>::on_initialize(*block_number);
		<frame_system::Module<System>>::register_extra_weight_unchecked(
			<AllModules as WeighBlock<System::BlockNumber>>::on_initialize(*block_number)
		);
		<frame_system::Module<System>>::register_extra_weight_unchecked(
			<AllModules as WeighBlock<System::BlockNumber>>::on_finalize(*block_number)
		);
	}

	fn initial_checks(block: &Block) {
		let header = block.header();

		// Check that `parent_hash` is correct.
		let n = header.number().clone();
		assert!(
			n > System::BlockNumber::zero()
			&& <frame_system::Module<System>>::block_hash(n - System::BlockNumber::one()) == *header.parent_hash(),
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
		<frame_system::Module<System>>::note_finished_extrinsics();
		<AllModules as OnFinalize<System::BlockNumber>>::on_finalize(block_number);
	}

	/// Finalize the block - it is up the caller to ensure that all header fields are valid
	/// except state-root.
	pub fn finalize_block() -> System::Header {
		<frame_system::Module<System>>::note_finished_extrinsics();
		<AllModules as OnFinalize<System::BlockNumber>>::on_finalize(<frame_system::Module<System>>::block_number());

		// set up extrinsics
		<frame_system::Module<System>>::derive_extrinsics();
		<frame_system::Module<System>>::finalize()
	}

	/// Apply extrinsic outside of the block execution function.
	///
	/// This doesn't attempt to validate anything regarding the block, but it builds a list of uxt
	/// hashes.
	pub fn apply_extrinsic(uxt: Block::Extrinsic) -> ApplyExtrinsicResult {
		let encoded = uxt.encode();
		let encoded_len = encoded.len();
		Self::apply_extrinsic_with_len(uxt, encoded_len, Some(encoded))
	}

	/// Apply an extrinsic inside the block execution function.
	fn apply_extrinsic_no_note(uxt: Block::Extrinsic) {
		let l = uxt.encode().len();
		match Self::apply_extrinsic_with_len(uxt, l, None) {
			Ok(_) => (),
			Err(e) => { let err: &'static str = e.into(); panic!(err) },
		}
	}

	/// Actually apply an extrinsic given its `encoded_len`; this doesn't note its hash.
	fn apply_extrinsic_with_len(
		uxt: Block::Extrinsic,
		encoded_len: usize,
		to_note: Option<Vec<u8>>,
	) -> ApplyExtrinsicResult {
		// Verify that the signature is good.
		let xt = uxt.check(&Default::default())?;

		// We don't need to make sure to `note_extrinsic` only after we know it's going to be
		// executed to prevent it from leaking in storage since at this point, it will either
		// execute or panic (and revert storage changes).
		if let Some(encoded) = to_note {
			<frame_system::Module<System>>::note_extrinsic(encoded);
		}

		// AUDIT: Under no circumstances may this function panic from here onwards.

		// Decode parameters and dispatch
		let dispatch_info = xt.get_dispatch_info();
		let r = Applyable::apply::<UnsignedValidator>(xt, dispatch_info, encoded_len)?;

		<frame_system::Module<System>>::note_applied_extrinsic(&r, encoded_len as u32, dispatch_info);

		Ok(r)
	}

	fn final_checks(header: &System::Header) {
		// remove temporaries
		let new_header = <frame_system::Module<System>>::finalize();

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
		let encoded_len = uxt.using_encoded(|d| d.len());
		let xt = uxt.check(&Default::default())?;

		let dispatch_info = xt.get_dispatch_info();
		xt.validate::<UnsignedValidator>(dispatch_info, encoded_len)
	}

	/// Start an offchain worker and generate extrinsics.
	pub fn offchain_worker(header: &System::Header) {
		// We need to keep events available for offchain workers,
		// hence we initialize the block manually.
		// OffchainWorker RuntimeApi should skip initialization.
		let digests = Self::extract_pre_digest(header);

		<frame_system::Module<System>>::initialize(
			header.number(),
			header.parent_hash(),
			header.extrinsics_root(),
			&digests,
			frame_system::InitKind::Inspection,
		);
		<AllModules as OffchainWorker<System::BlockNumber>>::offchain_worker(
			// to maintain backward compatibility we call module offchain workers
			// with parent block number.
			header.number().saturating_sub(1.into())
		)
	}
}


#[cfg(test)]
mod tests {
	use super::*;
	use sp_core::H256;
	use sp_runtime::{
		generic::Era, Perbill, DispatchError, testing::{Digest, Header, Block},
		traits::{Bounded, Header as HeaderT, BlakeTwo256, IdentityLookup, ConvertInto},
		transaction_validity::{InvalidTransaction, UnknownTransaction, TransactionValidityError},
	};
	use frame_support::{
		impl_outer_event, impl_outer_origin, parameter_types, impl_outer_dispatch,
		weights::Weight,
		traits::{Currency, LockIdentifier, LockableCurrency, WithdrawReasons, WithdrawReason},
	};
	use frame_system::{self as system, Call as SystemCall, ChainContext};
	use pallet_balances::Call as BalancesCall;
	use hex_literal::hex;

	mod custom {
		use frame_support::weights::SimpleDispatchInfo;

		pub trait Trait: frame_system::Trait {}

		frame_support::decl_module! {
			pub struct Module<T: Trait> for enum Call where origin: T::Origin {
				#[weight = SimpleDispatchInfo::FixedNormal(100)]
				fn some_function(origin) {
					// NOTE: does not make any different.
					let _ = frame_system::ensure_signed(origin);
				}
				#[weight = SimpleDispatchInfo::FixedOperational(200)]
				fn some_root_operation(origin) {
					let _ = frame_system::ensure_root(origin);
				}
				#[weight = SimpleDispatchInfo::InsecureFreeNormal]
				fn some_unsigned_message(origin) {
					let _ = frame_system::ensure_none(origin);
				}

				// module hooks.
				// one with block number arg and one without
				#[weight = SimpleDispatchInfo::FixedNormal(25)]
				fn on_initialize(n: T::BlockNumber) {
					println!("on_initialize({})", n);
				}
				#[weight = SimpleDispatchInfo::FixedNormal(150)]
				fn on_finalize() {
					println!("on_finalize(?)");
				}
			}
		}
	}

	type System = frame_system::Module<Runtime>;
	type Balances = pallet_balances::Module<Runtime>;
	type Custom = custom::Module<Runtime>;

	use pallet_balances as balances;

	impl_outer_origin! {
		pub enum Origin for Runtime { }
	}

	impl_outer_event!{
		pub enum MetaEvent for Runtime {
			balances<T>,
		}
	}
	impl_outer_dispatch! {
		pub enum Call for Runtime where origin: Origin {
			frame_system::System,
			pallet_balances::Balances,
		}
	}

	#[derive(Clone, Eq, PartialEq)]
	pub struct Runtime;
	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: Weight = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
	}
	impl frame_system::Trait for Runtime {
		type Origin = Origin;
		type Index = u64;
		type Call = Call;
		type BlockNumber = u64;
		type Hash = sp_core::H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<u64>;
		type Header = Header;
		type Event = MetaEvent;
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type AvailableBlockRatio = AvailableBlockRatio;
		type MaximumBlockLength = MaximumBlockLength;
		type Version = ();
		type ModuleToIndex = ();
	}
	parameter_types! {
		pub const ExistentialDeposit: u64 = 0;
		pub const CreationFee: u64 = 0;
	}
	impl pallet_balances::Trait for Runtime {
		type Balance = u64;
		type OnReapAccount = System;
		type OnNewAccount = ();
		type Event = MetaEvent;
		type DustRemoval = ();
		type TransferPayment = ();
		type ExistentialDeposit = ExistentialDeposit;
		type CreationFee = CreationFee;
	}

	parameter_types! {
		pub const TransactionBaseFee: u64 = 10;
		pub const TransactionByteFee: u64 = 0;
	}
	impl pallet_transaction_payment::Trait for Runtime {
		type Currency = Balances;
		type OnTransactionPayment = ();
		type TransactionBaseFee = TransactionBaseFee;
		type TransactionByteFee = TransactionByteFee;
		type WeightToFee = ConvertInto;
		type FeeMultiplierUpdate = ();
	}
	impl custom::Trait for Runtime {}

	#[allow(deprecated)]
	impl ValidateUnsigned for Runtime {
		type Call = Call;

		fn pre_dispatch(_call: &Self::Call) -> Result<(), TransactionValidityError> {
			Ok(())
		}

		fn validate_unsigned(call: &Self::Call) -> TransactionValidity {
			match call {
				Call::Balances(BalancesCall::set_balance(_, _, _)) => Ok(Default::default()),
				_ => UnknownTransaction::NoUnsignedValidator.into(),
			}
		}
	}

	type SignedExtra = (
		frame_system::CheckEra<Runtime>,
		frame_system::CheckNonce<Runtime>,
		frame_system::CheckWeight<Runtime>,
		pallet_transaction_payment::ChargeTransactionPayment<Runtime>
	);
	type AllModules = (System, Balances, Custom);
	type TestXt = sp_runtime::testing::TestXt<Call, SignedExtra>;
	type Executive = super::Executive<Runtime, Block<TestXt>, ChainContext<Runtime>, Runtime, AllModules>;

	fn extra(nonce: u64, fee: u64) -> SignedExtra {
		(
			frame_system::CheckEra::from(Era::Immortal),
			frame_system::CheckNonce::from(nonce),
			frame_system::CheckWeight::new(),
			pallet_transaction_payment::ChargeTransactionPayment::from(fee)
		)
	}

	fn sign_extra(who: u64, nonce: u64, fee: u64) -> Option<(u64, SignedExtra)> {
		Some((who, extra(nonce, fee)))
	}

	#[test]
	fn balance_transfer_dispatch_works() {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();
		pallet_balances::GenesisConfig::<Runtime> {
			balances: vec![(1, 211)],
		}.assimilate_storage(&mut t).unwrap();
		let xt = sp_runtime::testing::TestXt(sign_extra(1, 0, 0), Call::Balances(BalancesCall::transfer(2, 69)));
		let weight = xt.get_dispatch_info().weight as u64;
		let mut t = sp_io::TestExternalities::new(t);
		t.execute_with(|| {
			Executive::initialize_block(&Header::new(
				1,
				H256::default(),
				H256::default(),
				[69u8; 32].into(),
				Digest::default(),
			));
			let r = Executive::apply_extrinsic(xt);
			assert!(r.is_ok());
			assert_eq!(<pallet_balances::Module<Runtime>>::total_balance(&1), 142 - 10 - weight);
			assert_eq!(<pallet_balances::Module<Runtime>>::total_balance(&2), 69);
		});
	}

	fn new_test_ext(balance_factor: u64) -> sp_io::TestExternalities {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();
		pallet_balances::GenesisConfig::<Runtime> {
			balances: vec![(1, 111 * balance_factor)],
		}.assimilate_storage(&mut t).unwrap();
		t.into()
	}

	#[test]
	fn block_import_works() {
		new_test_ext(1).execute_with(|| {
			Executive::execute_block(Block {
				header: Header {
					parent_hash: [69u8; 32].into(),
					number: 1,
					state_root: hex!("a0b84fec49718caf59350dab6ec2993f12db399a7cccdb80f3cf79618ed93bd8").into(),
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
		new_test_ext(1).execute_with(|| {
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
		new_test_ext(1).execute_with(|| {
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
		let xt = sp_runtime::testing::TestXt(sign_extra(1, 30, 0), Call::Balances(BalancesCall::transfer(33, 69)));
		t.execute_with(|| {
			Executive::initialize_block(&Header::new(
				1,
				H256::default(),
				H256::default(),
				[69u8; 32].into(),
				Digest::default(),
			));
			assert!(Executive::apply_extrinsic(xt).is_err());
			assert_eq!(<frame_system::Module<Runtime>>::extrinsic_index(), Some(0));
		});
	}

	#[test]
	fn block_weight_limit_enforced() {
		let mut t = new_test_ext(10000);
		// given: TestXt uses the encoded len as fixed Len:
		let xt = sp_runtime::testing::TestXt(sign_extra(1, 0, 0), Call::Balances(BalancesCall::transfer(33, 0)));
		let encoded = xt.encode();
		let encoded_len = encoded.len() as Weight;
		let limit = AvailableBlockRatio::get() * MaximumBlockWeight::get() - 175;
		let num_to_exhaust_block = limit / encoded_len;
		t.execute_with(|| {
			Executive::initialize_block(&Header::new(
				1,
				H256::default(),
				H256::default(),
				[69u8; 32].into(),
				Digest::default(),
			));
			// Initial block weight form the custom module.
			assert_eq!(<frame_system::Module<Runtime>>::all_extrinsics_weight(), 175);

			for nonce in 0..=num_to_exhaust_block {
				let xt = sp_runtime::testing::TestXt(
					sign_extra(1, nonce.into(), 0), Call::Balances(BalancesCall::transfer(33, 0)),
				);
				let res = Executive::apply_extrinsic(xt);
				if nonce != num_to_exhaust_block {
					assert!(res.is_ok());
					assert_eq!(
						<frame_system::Module<Runtime>>::all_extrinsics_weight(),
						encoded_len * (nonce + 1) + 175,
					);
					assert_eq!(<frame_system::Module<Runtime>>::extrinsic_index(), Some(nonce as u32 + 1));
				} else {
					assert_eq!(res, Err(InvalidTransaction::ExhaustsResources.into()));
				}
			}
		});
	}

	#[test]
	fn block_weight_and_size_is_stored_per_tx() {
		let xt = sp_runtime::testing::TestXt(sign_extra(1, 0, 0), Call::Balances(BalancesCall::transfer(33, 0)));
		let x1 = sp_runtime::testing::TestXt(sign_extra(1, 1, 0), Call::Balances(BalancesCall::transfer(33, 0)));
		let x2 = sp_runtime::testing::TestXt(sign_extra(1, 2, 0), Call::Balances(BalancesCall::transfer(33, 0)));
		let len = xt.clone().encode().len() as u32;
		let mut t = new_test_ext(1);
		t.execute_with(|| {
			assert_eq!(<frame_system::Module<Runtime>>::all_extrinsics_weight(), 0);
			assert_eq!(<frame_system::Module<Runtime>>::all_extrinsics_weight(), 0);

			assert!(Executive::apply_extrinsic(xt.clone()).unwrap().is_ok());
			assert!(Executive::apply_extrinsic(x1.clone()).unwrap().is_ok());
			assert!(Executive::apply_extrinsic(x2.clone()).unwrap().is_ok());

			// default weight for `TestXt` == encoded length.
			assert_eq!(<frame_system::Module<Runtime>>::all_extrinsics_weight(), (3 * len) as Weight);
			assert_eq!(<frame_system::Module<Runtime>>::all_extrinsics_len(), 3 * len);

			let _ = <frame_system::Module<Runtime>>::finalize();

			assert_eq!(<frame_system::Module<Runtime>>::all_extrinsics_weight(), 0);
			assert_eq!(<frame_system::Module<Runtime>>::all_extrinsics_weight(), 0);
		});
	}

	#[test]
	fn validate_unsigned() {
		let xt = sp_runtime::testing::TestXt(None, Call::Balances(BalancesCall::set_balance(33, 69, 69)));
		let mut t = new_test_ext(1);

		t.execute_with(|| {
			assert_eq!(Executive::validate_transaction(xt.clone()), Ok(Default::default()));
			assert_eq!(Executive::apply_extrinsic(xt), Ok(Err(DispatchError::BadOrigin)));
		});
	}

	#[test]
	fn can_pay_for_tx_fee_on_full_lock() {
		let id: LockIdentifier = *b"0       ";
		let execute_with_lock = |lock: WithdrawReasons| {
			let mut t = new_test_ext(1);
			t.execute_with(|| {
				<pallet_balances::Module<Runtime> as LockableCurrency<u64>>::set_lock(
					id,
					&1,
					110,
					lock,
				);
				let xt = sp_runtime::testing::TestXt(
					sign_extra(1, 0, 0),
					Call::System(SystemCall::remark(vec![1u8])),
				);
				let weight = xt.get_dispatch_info().weight as u64;
				Executive::initialize_block(&Header::new(
					1,
					H256::default(),
					H256::default(),
					[69u8; 32].into(),
					Digest::default(),
				));

				if lock == WithdrawReasons::except(WithdrawReason::TransactionPayment) {
					assert!(Executive::apply_extrinsic(xt).unwrap().is_ok());
					// tx fee has been deducted.
					assert_eq!(<pallet_balances::Module<Runtime>>::total_balance(&1), 111 - 10 - weight);
				} else {
					assert_eq!(
						Executive::apply_extrinsic(xt),
						Err(InvalidTransaction::Payment.into()),
					);
					assert_eq!(<pallet_balances::Module<Runtime>>::total_balance(&1), 111);
				}
			});
		};

		execute_with_lock(WithdrawReasons::all());
		execute_with_lock(WithdrawReasons::except(WithdrawReason::TransactionPayment));
	}

	#[test]
	fn block_hooks_weight_is_stored() {
		new_test_ext(1).execute_with(|| {

			Executive::initialize_block(&Header::new_from_number(1));
			// NOTE: might need updates over time if system and balance introduce new weights. For
			// now only accounts for the custom module.
			assert_eq!(<frame_system::Module<Runtime>>::all_extrinsics_weight(), 150 + 25);
		})
	}
}
