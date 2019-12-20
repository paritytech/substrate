// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! # Utility Module
//! A module full of useful helpers for practical chain management.

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;
use codec::{Encode, Decode};
use sp_core::{TypeId, blake2_256};
use frame_support::{decl_module, decl_event, decl_error, decl_storage, Parameter, ensure};
use frame_support::{traits::{Get, ReservableCurrency, Currency}, weights::{
	SimpleDispatchInfo, GetDispatchInfo, ClassifyDispatch, WeighData, Weight, DispatchClass, PaysFee
}};
use frame_system::{self as system, ensure_root, ensure_signed};
use sp_runtime::{DispatchError, DispatchResult, traits::Dispatchable};

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

/// Configuration trait.
pub trait Trait: frame_system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;


	/// The overarching call type.
	type Call: Parameter + Dispatchable<Origin=Self::Origin> + GetDispatchInfo;

	/// The currency mechanism.
	type Currency: ReservableCurrency<Self::AccountId>;

	/// The amount of currency needed to reserve for creating a multisig execution.
	type MultisigDeposit: Get<BalanceOf<Self>>;

	/// The maximum amount of signatories allowed in the multisig.
	type MaxSignatories: Get<u16>;
}

decl_storage! {
	trait Store for Module<T: Trait> as Utility {
		/// The set of open multisig operations.
		pub Multisigs: double_map hasher(twox_64_concat) T::AccountId, twox_64_concat([u8; 32])
			=> Option<((T::BlockNumber, u32), BalanceOf<T>, T::AccountId, Vec<T::AccountId>)>;
	}
}

decl_error! {
	pub enum Error for Module<T: Trait> {
		/// Threshold is too low (zero).
		ZeroThreshold,
		/// Call is already approved by this signatory.
		AlreadyApproved,
		/// Call doesn't need any approvals as the threshold is just one.
		NoApprovalsNeeded,
		/// There are too many signatories in the list.
		TooManySignatories,
		/// Multisig operation not found when attempting to cancel.
		NotFound,
		/// Only the account that originally created the multisig is able to cancel it.
		NotOwner,
		/// No timepoint was given, yet the multisig operation is already underway.
		NoTimepoint,
		/// A different timepoint was given to the multisig operation that is underway.
		WrongTimepoint,
		/// A timepoint was given, yet no multisig operation is underway.
		UnexpectedTimepoint,
	}
}

decl_event! {
	/// Events type.
	pub enum Event<T> where
		AccountId = <T as system::Trait>::AccountId,
		BlockNumber = <T as system::Trait>::BlockNumber
	{
		BatchExecuted(Vec<Result<(), DispatchError>>),
		NewMultisig(AccountId, AccountId),
		MultisigApprove(BlockNumber, u32, AccountId, AccountId),
	}
}

/// Simple index-based pass through for the weight functions.
struct Passthrough<Call>(sp_std::marker::PhantomData<Call>);

impl<Call> Passthrough<Call> {
	fn new() -> Self { Self(Default::default()) }
}
impl<Call: GetDispatchInfo> WeighData<(&u16, &Box<Call>)> for Passthrough<Call> {
	fn weigh_data(&self, (_, call): (&u16, &Box<Call>)) -> Weight {
		call.get_dispatch_info().weight + 10_000
	}
}
impl<Call: GetDispatchInfo> ClassifyDispatch<(&u16, &Box<Call>)> for Passthrough<Call> {
	fn classify_dispatch(&self, (_, call): (&u16, &Box<Call>)) -> DispatchClass {
		call.get_dispatch_info().class
	}
}
impl<Call: GetDispatchInfo> PaysFee for Passthrough<Call> {
	fn pays_fee(&self) -> bool {
		true
	}
}

/// A point in time that no two transactions will share.
pub type Timepoint<T> = (<T as system::Trait>::BlockNumber, u32);

/// Simple index-based pass through for the weight functions.
struct PassthroughMulti<Call, AccountId, Timepoint>(
	sp_std::marker::PhantomData<(Call, AccountId, Timepoint)>
);

impl<Call, AccountId, Timepoint> PassthroughMulti<Call, AccountId, Timepoint> {
	fn new() -> Self { Self(Default::default()) }
}
impl<Call: GetDispatchInfo, AccountId, Timepoint> WeighData<(&u16, &Vec<AccountId>, &Timepoint, &Box<Call>)>
	for PassthroughMulti<Call, AccountId, Timepoint>
{
	fn weigh_data(&self, (_, _, _, call): (&u16, &Vec<AccountId>, &Timepoint, &Box<Call>)) -> Weight {
		call.get_dispatch_info().weight + 10_000
	}
}
impl<Call: GetDispatchInfo, AccountId, Timepoint> ClassifyDispatch<(&u16, &Vec<AccountId>, &Timepoint, &Box<Call>)>
	for PassthroughMulti<Call, AccountId, Timepoint>
{
	fn classify_dispatch(&self, (_, _, _, call): (&u16, &Vec<AccountId>, &Timepoint, &Box<Call>))
		-> DispatchClass
	{
		call.get_dispatch_info().class
	}
}
impl<Call: GetDispatchInfo, AccountId, Timepoint> PaysFee
	for PassthroughMulti<Call, AccountId, Timepoint>
{
	fn pays_fee(&self) -> bool {
		true
	}
}

/// A module identifier. These are per module and should be stored in a registry somewhere.
#[derive(Clone, Copy, Eq, PartialEq, Encode, Decode)]
struct IndexedUtilityModuleId(u16);

impl TypeId for IndexedUtilityModuleId {
	const TYPE_ID: [u8; 4] = *b"suba";
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		/// Deposit one of this module's events by using the default implementation.
		fn deposit_event() = default;

		/// Send a batch of dispatch calls (only root).
		// TODO: Should also pass through the weights.
		// TODO: Should not be restricted to Root origin; should duplicate the origin for each.
		#[weight = SimpleDispatchInfo::FreeOperational]
		fn batch(origin, calls: Vec<<T as Trait>::Call>) {
			ensure_root(origin)?;
			let results = calls.into_iter()
				.map(|call| call.dispatch(frame_system::RawOrigin::Root.into()))
				.map(|res| res.map_err(Into::into))
				.collect::<Vec<_>>();
			Self::deposit_event(Event::<T>::BatchExecuted(results));
		}

		/// Send a call through an indexed pseudonym of the sender.
		#[weight = <Passthrough<<T as Trait>::Call>>::new()]
		fn as_sub(origin, index: u16, call: Box<<T as Trait>::Call>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let pseudonym = Self::sub_account_id(who, index);
			call.dispatch(frame_system::RawOrigin::Signed(pseudonym).into())
		}

		/// Send a call from a deterministic composite account if approved by `threshold` of
		/// `signatories`.
		// TODO: make weight dependent on signatories len.
		#[weight = <PassthroughMulti<<T as Trait>::Call, T::AccountId, Option<(T::BlockNumber, u32)>>>::new()]
		fn as_multi(origin,
			threshold: u16,
			other_signatories: Vec<T::AccountId>,
			maybe_timepoint: Option<(T::BlockNumber, u32)>,
			call: Box<<T as Trait>::Call>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			ensure!(threshold >= 1, Error::<T>::ZeroThreshold);
			let max_sigs = T::MaxSignatories::get() as usize;
			ensure!(other_signatories.len() < max_sigs, Error::<T>::TooManySignatories);

			let mut signatories = other_signatories;
			signatories.push(who.clone());
			signatories.sort();

			let id = Self::multi_account_id(&signatories, threshold);
			let call_hash = call.using_encoded(blake2_256);

			if let Some((then, deposit, depositor, mut sigs)) = <Multisigs<T>>::get(&id, call_hash) {
				let timepoint = maybe_timepoint.ok_or(Error::<T>::NoTimepoint)?;
				ensure!(then == timepoint, Error::<T>::WrongTimepoint);
				if let Err(pos) = sigs.binary_search(&who) {
					if (sigs.len() as u16) + 1 < threshold {
						sigs.insert(pos, who);
						<Multisigs<T>>::insert(&id, call_hash, (then, deposit, depositor, sigs));
						return Ok(())
					}
				} else {
					if (sigs.len() as u16) < threshold {
						Err(Error::<T>::AlreadyApproved)?
					}
				}
				call.dispatch(frame_system::RawOrigin::Signed(id.clone()).into())?;
				let _ = T::Currency::unreserve(&depositor, deposit);
				<Multisigs<T>>::remove(&id, call_hash);
			} else {
				ensure!(maybe_timepoint.is_none(), Error::<T>::UnexpectedTimepoint);
				if threshold > 1 {
					let deposit = T::MultisigDeposit::get();
					T::Currency::reserve(&who, deposit)?;
					let now = Self::timepoint();
					<Multisigs<T>>::insert(&id, call_hash, (now, deposit, who.clone(), vec![who]));
				} else {
					call.dispatch(frame_system::RawOrigin::Signed(id).into())?;
				}
			}
			Ok(())
		}

		/// Cancel a pre-existing, on-going multisig transaction.
		#[weight = SimpleDispatchInfo::FixedNormal(10_000)]
		fn cancel_as_multi(origin,
			threshold: u16,
			other_signatories: Vec<T::AccountId>,
			timepoint: (T::BlockNumber, u32),
			call_hash: [u8; 32]
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			ensure!(threshold >= 1, Error::<T>::ZeroThreshold);
			let max_sigs = T::MaxSignatories::get() as usize;
			ensure!(other_signatories.len() < max_sigs, Error::<T>::TooManySignatories);

			let mut signatories = other_signatories;
			signatories.push(who.clone());
			signatories.sort();

			let id = Self::multi_account_id(&signatories, threshold);

			let (then, deposit, depositor, _) = <Multisigs<T>>::get(&id, call_hash)
				.ok_or(Error::<T>::NotFound)?;
			ensure!(then == timepoint, Error::<T>::WrongTimepoint);
			ensure!(depositor == who, Error::<T>::NotOwner);

			let _ = T::Currency::unreserve(&depositor, deposit);
			<Multisigs<T>>::remove(&id, call_hash);
			Ok(())
		}

		/// Send a call through an indexed pseudonym of the sender.
		#[weight = SimpleDispatchInfo::FixedNormal(10_000)]
		// TODO: make weight dependent on signatories len.
		fn approve_as_multi(origin,
			threshold: u16,
			other_signatories: Vec<T::AccountId>,
			maybe_timepoint: Option<(T::BlockNumber, u32)>,
			call_hash: [u8; 32],
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			ensure!(threshold >= 1, Error::<T>::ZeroThreshold);
			let max_sigs = T::MaxSignatories::get() as usize;
			ensure!(other_signatories.len() < max_sigs, Error::<T>::TooManySignatories);

			let mut signatories = other_signatories;
			signatories.push(who.clone());
			signatories.sort();

			let id = Self::multi_account_id(&signatories, threshold);

			if let Some((then, deposit, depositor, mut sigs)) = <Multisigs<T>>::get(&id, call_hash) {
				let timepoint = maybe_timepoint.ok_or(Error::<T>::NoTimepoint)?;
				ensure!(then == timepoint, Error::<T>::WrongTimepoint);
				if let Err(pos) = sigs.binary_search(&who) {
					sigs.insert(pos, who);
					<Multisigs<T>>::insert(id, call_hash, (then, deposit, depositor, sigs));
					return Ok(())
				} else {
					Err(Error::<T>::AlreadyApproved)?
				}
			} else {
				if threshold > 1 {
					ensure!(maybe_timepoint.is_none(), Error::<T>::UnexpectedTimepoint);
					let deposit = T::MultisigDeposit::get();
					T::Currency::reserve(&who, deposit)?;
					let now = Self::timepoint();
					<Multisigs<T>>::insert(id, call_hash, (now, deposit, who.clone(), vec![who]));
					return Ok(())
				} else {
					Err(Error::<T>::NoApprovalsNeeded)?
				}
			}
		}
	}
}

impl<T: Trait> Module<T> {
	pub fn sub_account_id(who: T::AccountId, index: u16) -> T::AccountId {
		let entropy = (b"modlpy/utilisuba", who, index).using_encoded(blake2_256);
		T::AccountId::decode(&mut &entropy[..]).unwrap_or_default()
	}

	pub fn multi_account_id(who: &[T::AccountId], threshold: u16) -> T::AccountId {
		let entropy = (b"modlpy/utilisuba", who, threshold).using_encoded(blake2_256);
		T::AccountId::decode(&mut &entropy[..]).unwrap_or_default()
	}

	pub fn timepoint() -> (T::BlockNumber, u32) {
		(<system::Module<T>>::block_number(), <system::Module<T>>::extrinsic_count())
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use frame_support::{
		assert_ok, assert_noop, impl_outer_origin, parameter_types, impl_outer_dispatch,
		weights::Weight
	};
	use sp_core::H256;
	use sp_runtime::{Perbill, traits::{BlakeTwo256, IdentityLookup, BadOrigin}, testing::Header};

	impl_outer_origin! {
		pub enum Origin for Test  where system = frame_system {}
	}

	impl_outer_dispatch! {
		pub enum Call for Test where origin: Origin {
			pallet_balances::Balances,
			utility::Utility,
		}
	}

	// For testing the module, we construct most of a mock runtime. This means
	// first constructing a configuration type (`Test`) which `impl`s each of the
	// configuration traits of modules we want to use.
	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: Weight = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
	}
	impl frame_system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Call = Call;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type MaximumBlockLength = MaximumBlockLength;
		type AvailableBlockRatio = AvailableBlockRatio;
		type Version = ();
		type ModuleToIndex = ();
	}
	parameter_types! {
		pub const ExistentialDeposit: u64 = 0;
		pub const TransferFee: u64 = 0;
		pub const CreationFee: u64 = 0;
	}
	impl pallet_balances::Trait for Test {
		type Balance = u64;
		type OnFreeBalanceZero = ();
		type OnNewAccount = ();
		type Event = ();
		type TransferPayment = ();
		type DustRemoval = ();
		type ExistentialDeposit = ExistentialDeposit;
		type TransferFee = TransferFee;
		type CreationFee = CreationFee;
	}
	parameter_types! {
		pub const MultisigDeposit: u64 = 0;
		pub const MaxSignatories: u16 = 3;
	}
	impl Trait for Test {
		type Event = ();
		type Call = Call;
		type Currency = Balances;
		type MultisigDeposit = MultisigDeposit;
		type MaxSignatories = MaxSignatories;
	}
	type Balances = pallet_balances::Module<Test>;
	type Utility = Module<Test>;

	use pallet_balances::Call as BalancesCall;
	use pallet_balances::Error as BalancesError;

	fn new_test_ext() -> sp_io::TestExternalities {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		pallet_balances::GenesisConfig::<Test> {
			balances: vec![(1, 10), (2, 10), (3, 10), (4, 10), (5, 10)],
			vesting: vec![],
		}.assimilate_storage(&mut t).unwrap();
		t.into()
	}

	#[test]
	fn timepoint_checking_works() {
		new_test_ext().execute_with(|| {
			let multi = Utility::multi_account_id(&[1, 2, 3][..], 2);
			assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			let hash = call.using_encoded(blake2_256);

			assert_noop!(
				Utility::approve_as_multi(Origin::signed(2), 2, vec![1, 3], Some((1, 0)), hash.clone()),
				Error::<Test>::UnexpectedTimepoint,
			);

			assert_ok!(Utility::approve_as_multi(Origin::signed(1), 2, vec![2, 3], None, hash));

			assert_noop!(
				Utility::as_multi(Origin::signed(2), 2, vec![1, 3], None, call.clone()),
				Error::<Test>::NoTimepoint,
			);
			assert_noop!(
				Utility::as_multi(Origin::signed(2), 2, vec![1, 3], Some((1, 1)), call.clone()),
				Error::<Test>::WrongTimepoint,
			);
		});
	}

	#[test]
	fn multisig_2_of_3_works() {
		new_test_ext().execute_with(|| {
			let multi = Utility::multi_account_id(&[1, 2, 3][..], 2);
			assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			let hash = call.using_encoded(blake2_256);
			assert_ok!(Utility::approve_as_multi(Origin::signed(1), 2, vec![2, 3], None, hash));
			assert_eq!(Balances::free_balance(6), 0);

			assert_ok!(Utility::as_multi(Origin::signed(2), 2, vec![1, 3], Some((1, 0)), call));
			assert_eq!(Balances::free_balance(6), 15);
		});
	}

	#[test]
	fn multisig_3_of_3_works() {
		new_test_ext().execute_with(|| {
			let multi = Utility::multi_account_id(&[1, 2, 3][..], 3);
			assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			let hash = call.using_encoded(blake2_256);
			assert_ok!(Utility::approve_as_multi(Origin::signed(1), 3, vec![2, 3], None, hash.clone()));
			assert_ok!(Utility::approve_as_multi(Origin::signed(2), 3, vec![1, 3], Some((1, 0)), hash.clone()));
			assert_eq!(Balances::free_balance(6), 0);

			assert_ok!(Utility::as_multi(Origin::signed(3), 3, vec![1, 2], Some((1, 0)), call));
			assert_eq!(Balances::free_balance(6), 15);
		});
	}

	#[test]
	fn cancel_multisig_works() {
		new_test_ext().execute_with(|| {
			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			let hash = call.using_encoded(blake2_256);
			assert_ok!(Utility::approve_as_multi(Origin::signed(1), 3, vec![2, 3], None, hash.clone()));
			assert_ok!(Utility::approve_as_multi(Origin::signed(2), 3, vec![1, 3], Some((1, 0)), hash.clone()));
			assert_noop!(
				Utility::as_multi(Origin::signed(3), 3, vec![1, 2], Some((1, 0)), call),
				BalancesError::<Test, _>::InsufficientBalance,
			);
			assert_noop!(
				Utility::cancel_as_multi(Origin::signed(2), 3, vec![1, 3], (1, 0), hash.clone()),
				Error::<Test>::NotOwner,
			);
			assert_ok!(
				Utility::cancel_as_multi(Origin::signed(1), 3, vec![2, 3], (1, 0), hash.clone()),
			);
		});
	}

	#[test]
	fn multisig_2_of_3_as_multi_works() {
		new_test_ext().execute_with(|| {
			let multi = Utility::multi_account_id(&[1, 2, 3][..], 2);
			assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			assert_ok!(Utility::as_multi(Origin::signed(1), 2, vec![2, 3], None, call.clone()));
			assert_eq!(Balances::free_balance(6), 0);

			assert_ok!(Utility::as_multi(Origin::signed(2), 2, vec![1, 3], Some((1, 0)), call));
			assert_eq!(Balances::free_balance(6), 15);
		});
	}

	#[test]
	fn multisig_2_of_3_as_multi_with_many_calls_works() {
		new_test_ext().execute_with(|| {
			let multi = Utility::multi_account_id(&[1, 2, 3][..], 2);
			assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

			let call1 = Box::new(Call::Balances(BalancesCall::transfer(6, 10)));
			let call2 = Box::new(Call::Balances(BalancesCall::transfer(7, 5)));

			assert_ok!(Utility::as_multi(Origin::signed(1), 2, vec![2, 3], None, call1.clone()));
			assert_ok!(Utility::as_multi(Origin::signed(2), 2, vec![1, 3], None, call2.clone()));
			assert_ok!(Utility::as_multi(Origin::signed(3), 2, vec![1, 2], Some((1, 0)), call2));
			assert_ok!(Utility::as_multi(Origin::signed(3), 2, vec![1, 2], Some((1, 0)), call1));

			assert_eq!(Balances::free_balance(6), 10);
			assert_eq!(Balances::free_balance(7), 5);
		});
	}

	#[test]
	fn multisig_2_of_3_reissue_same_call_works() {
		new_test_ext().execute_with(|| {
			let multi = Utility::multi_account_id(&[1, 2, 3][..], 2);
			assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 10)));
			assert_ok!(Utility::as_multi(Origin::signed(1), 2, vec![2, 3], None, call.clone()));
			assert_ok!(Utility::as_multi(Origin::signed(2), 2, vec![1, 3], Some((1, 0)), call.clone()));
			assert_eq!(Balances::free_balance(multi), 5);

			assert_ok!(Utility::as_multi(Origin::signed(1), 2, vec![2, 3], None, call.clone()));
			assert_noop!(
				Utility::as_multi(Origin::signed(3), 2, vec![1, 2], Some((1, 0)), call),
				BalancesError::<Test, _>::InsufficientBalance,
			);
		});
	}

	#[test]
	fn zero_threshold_fails() {
		new_test_ext().execute_with(|| {
			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			assert_noop!(
				Utility::as_multi(Origin::signed(1), 0, vec![2], None, call),
				Error::<Test>::ZeroThreshold,
			);
		});
	}

	#[test]
	fn too_many_signatories_fails() {
		new_test_ext().execute_with(|| {
			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			assert_noop!(
				Utility::as_multi(Origin::signed(1), 2, vec![2, 3, 4], None, call.clone()),
				Error::<Test>::TooManySignatories,
			);
		});
	}

	#[test]
	fn duplicate_approvals_are_ignored() {
		new_test_ext().execute_with(|| {
			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			let hash = call.using_encoded(blake2_256);
			assert_ok!(Utility::approve_as_multi(Origin::signed(1), 2, vec![2, 3], None, hash.clone()));
			assert_ok!(Utility::approve_as_multi(Origin::signed(2), 2, vec![1, 3], Some((1, 0)), hash.clone()));
			assert_noop!(
				Utility::approve_as_multi(Origin::signed(1), 2, vec![2, 3], Some((1, 0)), hash.clone()),
				Error::<Test>::AlreadyApproved,
			);
			assert_noop!(
				Utility::approve_as_multi(Origin::signed(2), 2, vec![1, 3], Some((1, 0)), hash.clone()),
				Error::<Test>::AlreadyApproved,
			);
		});
	}

	#[test]
	fn multisig_1_of_3_works() {
		new_test_ext().execute_with(|| {
			let multi = Utility::multi_account_id(&[1, 2, 3][..], 1);
			assert_ok!(Balances::transfer(Origin::signed(1), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(2), multi, 5));
			assert_ok!(Balances::transfer(Origin::signed(3), multi, 5));

			let call = Box::new(Call::Balances(BalancesCall::transfer(6, 15)));
			let hash = call.using_encoded(blake2_256);
			assert_noop!(
				Utility::approve_as_multi(Origin::signed(1), 1, vec![2, 3], None, hash.clone()),
				Error::<Test>::NoApprovalsNeeded,
			);
			assert_noop!(
				Utility::as_multi(Origin::signed(4), 1, vec![2, 3], None, call.clone()),
				BalancesError::<Test, _>::InsufficientBalance,
			);
			assert_ok!(Utility::as_multi(Origin::signed(1), 1, vec![2, 3], None, call));

			assert_eq!(Balances::free_balance(6), 15);
		});
	}

	#[test]
	fn as_sub_works() {
		new_test_ext().execute_with(|| {
			let sub_1_0 = Utility::sub_account_id(1, 0);
			assert_ok!(Balances::transfer(Origin::signed(1), sub_1_0, 5));
			assert_noop!(Utility::as_sub(
				Origin::signed(1),
				1,
				Box::new(Call::Balances(BalancesCall::transfer(6, 3))),
			), BalancesError::<Test, _>::InsufficientBalance);
			assert_ok!(Utility::as_sub(
				Origin::signed(1),
				0,
				Box::new(Call::Balances(BalancesCall::transfer(2, 3))),
			));
			assert_eq!(Balances::free_balance(sub_1_0), 2);
			assert_eq!(Balances::free_balance(2), 13);
		});
	}

	#[test]
	fn batch_works() {
		new_test_ext().execute_with(|| {
			assert_eq!(Balances::free_balance(1), 10);
			assert_eq!(Balances::free_balance(2), 10);
			assert_noop!(
				Utility::batch(Origin::signed(1), vec![
					Call::Balances(BalancesCall::force_transfer(1, 2, 5)),
					Call::Balances(BalancesCall::force_transfer(1, 2, 5))
				]),
				BadOrigin,
			);
			assert_ok!(Utility::batch(Origin::ROOT, vec![
				Call::Balances(BalancesCall::force_transfer(1, 2, 5)),
				Call::Balances(BalancesCall::force_transfer(1, 2, 5))
			]));
			assert_eq!(Balances::free_balance(1), 0);
			assert_eq!(Balances::free_balance(2), 20);
		});
	}
}
