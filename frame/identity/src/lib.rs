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

//! # Identity Module
//!
//! - [`identity::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//!
//! ## Overview
//!
//! A federated naming system, allowing for multiple registrars to be added from a specified origin.
//! Registrars can set a fee to provide identity-verification service. Anyone can put forth a
//! proposed identity for a fixed deposit and ask for review by any number of registrars (paying
//! each of their fees). Registrar judgements are multi-tier allowing for more sophisticated
//! opinions than a boolean true or false.
//!
//! A super-user can remove accounts and slash the deposit.
//!
//! All accounts may also have a limited number of sub-accounts which have equivalent ownership.
//!
//! The number of registrars should be limited, and the deposit made sufficiently large, to ensure
//! no state-bloat attack is viable.
//!
//!
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! * `set_identity` - Set the associated identity of an account; a small deposit is reserved if not already
//!   taken.
//! * `clear_identity` - Remove an account's associated identity; the deposit is returned.
//! * `kill_identity` - Forcibly remove the associated identity; the deposit is lost.
//!
//! [`Call`]: ./enum.Call.html
//! [`Trait`]: ./trait.Trait.html

#![cfg_attr(not(feature = "std"), no_std)]

use rstd::prelude::*;
use rstd::{fmt::Debug, ops::Add};
use sp_runtime::{
	traits::{StaticLookup, EnsureOrigin, Zero}, RuntimeDebug,
};
use codec::{Encode, Decode};
use support::{
	decl_module, decl_event, decl_storage, ensure, dispatch::Result,
	traits::{Currency, ReservableCurrency, OnUnbalanced, Get},
	weights::SimpleDispatchInfo,
};
use system::{ensure_signed, ensure_root};

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;
type NegativeImbalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::NegativeImbalance;

pub trait Trait: system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	/// The currency trait.
	type Currency: ReservableCurrency<Self::AccountId>;

	/// The amount held on deposit for a registered identity.
	type BasicDeposit: Get<BalanceOf<Self>>;

	/// The amount held on deposit per additional field for a registered identity.
	type FieldDeposit: Get<BalanceOf<Self>>;

	/// The amount held on deposit for a registered subaccount.
	type SubAccountDeposit: Get<BalanceOf<Self>>;

	/// The amount held on deposit for a registered subaccount.
	type MaximumSubAccounts: Get<u32>;

	/// What to do with slashed funds.
	type Slashed: OnUnbalanced<NegativeImbalanceOf<Self>>;

	/// The origin which may forcibly set or remove a name. Root can always do this.
	type ForceOrigin: EnsureOrigin<Self::Origin>;

	/// The origin which may add or remove registrars. Root can always do this.
	type RegistrarOrigin: EnsureOrigin<Self::Origin>;
}

/// Either underlying data or a hash of it, if the data is less than 32 bytes.
///
/// Can also be `None`.
#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug)]
pub enum Data<Hash: Encode + Decode + Clone + Debug + Eq + PartialEq> {
	/// No data here.
	None,
	/// The data is stored directly.
	Raw(Vec<u8>),
	/// Only a hash of the data is stored. The preimage of the hash may be retrieved through
	/// some hash-lookup service.
	Hash(Hash),
}

/// An identifier for a single name registrar/identity verification service.
pub type RegistrarIndex = u32;

/// An opinion of a registrar over how accurate some `IdentityInfo` is in describing an account.
#[derive(Copy, Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug)]
pub enum Judgement<
	Balance: Encode + Decode + Copy + Clone + Debug + Eq + PartialEq
> {
	/// The default value; no opinion is held.
	Unknown,
	/// No judgement is yet in place, but a deposit is reserved as payment for providing one.
	FeePaid(Balance),
	/// The data appears to be reasonably acceptable in terms of its accuracy, however no in depth
	/// checks (such as in-person meetings or formal KYC) have been conducted.
	Reasonable,
	/// The target is known directly by the registrar and can fully attest to being accurate.
	KnownGood,
	/// The data was once good but is currently out of date. There is no malicious intent in the
	/// inaccuracy. This judgement can be removed through updating the data.
	OutOfDate,
	/// The data is imprecise or of sufficiently low-quality to be problematic. It is not
	/// indicative of malicious intent. This judgement can be removed through updating the data.
	LowQuality,
	/// The data is erroneous. This may be indicative of malicious intent. This cannot be removed
	/// except by the registrar.
	Erroneous,
}

impl<
	Balance: Encode + Decode + Copy + Clone + Debug + Eq + PartialEq
> Judgement<Balance> {
	fn is_evil(&self) -> bool {
		match self {
			Judgement::Erroneous => true,
			_ => false,
		}
	}

	fn has_deposit(&self) -> bool {
		match self {
			Judgement::FeePaid(_) => true,
			_ => false,
		}
	}

	fn is_sticky(&self) -> bool {
		match self {
			Judgement::FeePaid(_) | Judgement::Erroneous => true,
			_ => false,
		}
	}
}

/// Information concerning the identity of the controller of an account.
///
/// NOTE: This should be stored at the end of the storage item to facilitate the addition of extra
/// fields in a backwards compatible way through a specialised `Decode` impl.
#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug)]
pub struct IdentityInfo<
	Hash: Encode + Decode + Clone + Debug + Eq + PartialEq
> {
	/// Additional fields of the identity that are not catered for with the structs explicit
	/// fields. Stored ordered.
	pub additional: Vec<(Data<Hash>, Data<Hash>)>,

	/// A reasonable display name for the controller of the account. This should be whatever is it
	/// that it is typically known as and should not be confusable with other entities, given
	/// reasonable context.
	///
	/// Stored as UTF-8.
	pub display: Data<Hash>,

	/// The full legal name in the local jurisdiction of the entity. This might be a bit
	/// long-winded.
	///
	/// Stored as UTF-8.
	pub legal: Data<Hash>,

	/// A representative website held by the controller of the account.
	///
	/// NOTE: `https://` is automatically prepended.
	///
	/// Stored as 7-bit ASCII.
	pub web: Data<Hash>,

	/// The Riot handle held by the controller of the account.
	///
	/// Stored as 7-bit ASCII.
	pub riot: Data<Hash>,

	/// The email address of the controller of the account.
	///
	/// Stored as 7-bit ASCII.
	pub email: Data<Hash>,

	/// The PGP/GPG public key of the controller of the account.
	pub pgp_fingerprint: Option<[u8; 20]>,
}

/// Information concerning the identity of the controller of an account.
///
/// NOTE: This is stored separately primarily to facilitate the addition of extra fields in a
/// backwards compatible way through a specialised `Decode` impl.
#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug)]
pub struct Registration<
	Balance: Encode + Decode + Copy + Clone + Debug + Eq + PartialEq,
	Hash: Encode + Decode + Clone + Debug + Eq + PartialEq
> {
	/// Judgements from the registrars on this identity. Stored ordered by RegistrarIndex. There
	/// may be only a single judgement from each registrar.
	pub judgements: Vec<(RegistrarIndex, Judgement<Balance>)>,

	/// Amount held on deposit for this information.
	pub deposit: Balance,

	/// Information on the identity.
	pub info: IdentityInfo<Hash>,
}

impl <
	Balance: Encode + Decode + Copy + Clone + Debug + Eq + PartialEq + Zero + Add,
	Hash: Encode + Decode + Clone + Debug + Eq + PartialEq
> Registration<Balance, Hash> {
	fn total_deposit(&self) -> Balance {
		self.deposit + self.judgements.iter()
			.map(|(_, ref j)| if let Judgement::FeePaid(fee) = j { *fee } else { Zero::zero() })
			.fold(Zero::zero(), |a, i| a + i)
	}
}

/// Information concerning the a registrar.
#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug)]
pub struct RegistrarInfo<
	Balance: Encode + Decode + Clone + Debug + Eq + PartialEq,
	AccountId: Encode + Decode + Clone + Debug + Eq + PartialEq
> {
	/// The account of the registrar.
	pub account: AccountId,

	/// Amount required to be given to the registrar for them to check the account.
	pub fee: Balance,
}

decl_storage! {
	trait Store for Module<T: Trait> as Sudo {
		/// Information that is pertinent to an account. Registrer
		IdentityOf: map T::AccountId => Option<Registration<BalanceOf<T>, T::Hash>>;

		/// Alternative "sub" identites of this account.
		SubsOf: map T::AccountId => (BalanceOf<T>, Vec<(T::AccountId, Data<T::Hash>)>);

		/// The set of registrars. Not expected to get very big as can only be added through a
		/// special origin (likely a council motion).
		///
		/// The index into this can be cast to `RegistrarIndex` to get a valid value.
		Registrars: Vec<Option<RegistrarInfo<BalanceOf<T>, T::AccountId>>>;
	}
}

decl_event!(
	pub enum Event<T> where AccountId = <T as system::Trait>::AccountId, Balance = BalanceOf<T> {
		/// A name was set or reset (which will remove all judgements).
		IdentitySet(AccountId),
		/// A name was forcibly set.
		IdentityForced(AccountId),
		/// A name was cleared, and the given balance returned.
		IdentityCleared(AccountId, Balance),
		/// A name was removed and the given balance slashed.
		IdentityKilled(AccountId, Balance),
		/// A judgement was asked from a registrar.
		JudgementRequested(AccountId, RegistrarIndex),
		/// A judgement request was retracted.
		JudgementUnrequested(AccountId, RegistrarIndex),
		/// A judgement was given by a registrar.
		JudgementGiven(AccountId, RegistrarIndex),
		/// A registrar was added.
		RegistrarAdded(RegistrarIndex),
		/// A registrar was removed.
		RegistrarRemvoed(RegistrarIndex),
	}
);

decl_module! {
	// Simple declaration of the `Module` type. Lets the macro know what it's working on.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event() = default;

		#[weight = SimpleDispatchInfo::FixedNormal(50_000)]
		fn add_registrar(origin, account: T::AccountId) {
			T::RegistrarOrigin::try_origin(origin)
				.map(|_| ())
				.or_else(ensure_root)
				.map_err(|_| "bad origin")?;

			let i = <Registrars<T>>::mutate(|r| {
				r.push(Some(RegistrarInfo { account, fee: Zero::zero() }));
				(r.len() - 1) as RegistrarIndex
			});

			Self::deposit_event(RawEvent::RegistrarAdded(i));
		}

		/// Set an account's identity information.
		///
		/// If the account doesn't already have a name, then a fee of `ReservationFee` is reserved
		/// in the account.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// # <weight>
		/// - O(1).
		/// - At most two balance operations.
		/// - One storage read/write.
		/// - One event.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(50_000)]
		fn set_identity(origin, info: IdentityInfo<T::Hash>) {
			let sender = ensure_signed(origin)?;
			let fd = <BalanceOf<T>>::from(info.additional.len() as u32) * T::FieldDeposit::get();
			let mut id = match <IdentityOf<T>>::get(&sender) {
				Some(mut id) => {
					// Only keep non-positive judgements.
					id.judgements.retain(|j| j.1.is_sticky());
					// Return the deposit, if possible.
					let _ = T::Currency::unreserve(&sender, id.deposit);
					id.info = info;
					id
				}
				None => Registration { info, judgements: Vec::new(), deposit: Zero::zero() },
			};

			id.deposit = T::BasicDeposit::get() + fd;
			T::Currency::reserve(&sender, id.deposit)?;

			<IdentityOf<T>>::insert(&sender, id);
			Self::deposit_event(RawEvent::IdentitySet(sender));
		}

		/// Set the sub-accounts of the sender.
		///
		/// The sender must have a registered identity.
		///
		/// The dispatch origin for this call must be _Signed_.
		fn set_subs(origin, subs: Vec<(T::AccountId, Data<T::Hash>)>) {
			let sender = ensure_signed(origin)?;
			ensure!(<IdentityOf<T>>::exists(&sender), "not found");
			ensure!(subs.len() <= T::MaximumSubAccounts::get() as usize, "too many subs");

			let old_deposit = <SubsOf<T>>::get(&sender).0;
			let new_deposit = T::SubAccountDeposit::get() * <BalanceOf<T>>::from(subs.len() as u32);

			if old_deposit < new_deposit {
				T::Currency::reserve(&sender, new_deposit - old_deposit)?;
			}
			// do nothing if they're equal.
			if old_deposit > new_deposit {
				let _ = T::Currency::unreserve(&sender, old_deposit - new_deposit);
			}

			if subs.is_empty() {
				<SubsOf<T>>::remove(&sender);
			} else {
				<SubsOf<T>>::insert(&sender, (new_deposit, subs));
			}
		}

		/// Clear an account's identity info and return the deposit. Fails if the account was not
		/// named. All sub-accounts are removed also.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// # <weight>
		/// - O(1).
		/// - One balance operation.
		/// - One storage read/write.
		/// - One event.
		/// # </weight>
		fn clear_identity(origin) {
			let sender = ensure_signed(origin)?;

			let deposit = <IdentityOf<T>>::take(&sender).ok_or("not found")?.deposit;

			let _ = T::Currency::unreserve(&sender, deposit.clone());

			Self::deposit_event(RawEvent::IdentityCleared(sender, deposit));
		}

		/// Ask for a judgement from a registrar. A fee will be taken.
		#[weight = SimpleDispatchInfo::FixedNormal(50_000)]
		fn ask_judgement(origin, reg_index: RegistrarIndex) {
			let sender = ensure_signed(origin)?;
			let registrars = <Registrars<T>>::get();
			let registrar = registrars.get(reg_index as usize).and_then(Option::as_ref)
				.ok_or("empty index")?;
			let mut id = <IdentityOf<T>>::get(&sender).ok_or("no identity")?;

			T::Currency::reserve(&sender, registrar.fee)?;

			let item = (reg_index, Judgement::FeePaid(registrar.fee));
			match id.judgements.binary_search_by_key(&reg_index, |x| x.0) {
				Ok(i) => if id.judgements[i].1.is_evil() {
					return Err("evil account")
				} else {
					id.judgements[i] = item
				},
				Err(i) => id.judgements.insert(i, item),
			}

			<IdentityOf<T>>::insert(&sender, id);

			Self::deposit_event(RawEvent::JudgementRequested(sender, reg_index));
		}

		#[weight = SimpleDispatchInfo::FixedNormal(50_000)]
		fn unask_judgement(origin, reg_index: RegistrarIndex) {
			let sender = ensure_signed(origin)?;
			let mut id = <IdentityOf<T>>::get(&sender).ok_or("no identity")?;

			let pos = id.judgements.binary_search_by_key(&reg_index, |x| x.0)
				.map_err(|_| "not found")?;
			let fee = if let Judgement::FeePaid(fee) = id.judgements.remove(pos).1 {
				fee
			} else {
				return Err("judgement given")
			};

			let _ = T::Currency::unreserve(&sender, fee);
			<IdentityOf<T>>::insert(&sender, id);

			Self::deposit_event(RawEvent::JudgementUnrequested(sender, reg_index));
		}

		#[weight = SimpleDispatchInfo::FixedNormal(50_000)]
		fn set_fee(origin,
			#[compact] index: RegistrarIndex,
			#[compact] fee: BalanceOf<T>
		) -> Result {
			let who = ensure_signed(origin)?;

			<Registrars<T>>::mutate(|rs|
				rs.get_mut(index as usize)
					.and_then(|x| x.as_mut())
					.and_then(|r| if r.account == who { r.fee = fee; Some(()) } else { None })
					.ok_or("invalid index")
			)
		}

		#[weight = SimpleDispatchInfo::FixedNormal(50_000)]
		fn provide_judgement(origin,
			#[compact] reg_index: RegistrarIndex,
			target: <T::Lookup as StaticLookup>::Source,
			judgement: Judgement<BalanceOf<T>>
		) {
			let sender = ensure_signed(origin)?;
			let target = T::Lookup::lookup(target)?;
			ensure!(!judgement.has_deposit(), "invalid judgement");
			<Registrars<T>>::get()
				.get(reg_index as usize)
				.and_then(Option::as_ref)
				.and_then(|r| if r.account == sender { Some(r) } else { None })
				.ok_or("invalid index")?;
			let mut id = <IdentityOf<T>>::get(&target).ok_or("invalid target")?;

			let item = (reg_index, judgement);
			match id.judgements.binary_search_by_key(&reg_index, |x| x.0) {
				Ok(position) => {
					if let Judgement::FeePaid(fee) = id.judgements[position].1 {
						let _ = T::Currency::repatriate_reserved(&target, &sender, fee);
					}
					id.judgements[position] = item
				}
				Err(position) => id.judgements.insert(position, item),
			}
			<IdentityOf<T>>::insert(&target, id);
			Self::deposit_event(RawEvent::JudgementGiven(target, reg_index));
		}

		/// Remove an account's name and take charge of the deposit.
		///
		/// Fails if `who` has not been named. The deposit is dealt with through `T::Slashed`
		/// imbalance handler.
		///
		/// The dispatch origin for this call must be _Root_ or match `T::ForceOrigin`.
		///
		/// # <weight>
		/// - O(1).
		/// - One unbalanced handler (probably a balance transfer)
		/// - One storage read/write.
		/// - One event.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FreeOperational]
		fn kill_identity(origin, target: <T::Lookup as StaticLookup>::Source) {
			T::ForceOrigin::try_origin(origin)
				.map(|_| ())
				.or_else(ensure_root)
				.map_err(|_| "bad origin")?;

			// Figure out who we're meant to be clearing.
			let target = T::Lookup::lookup(target)?;
			// Grab their deposit (and check that they have one).
			let deposit = <IdentityOf<T>>::take(&target).ok_or("Not named")?.total_deposit()
				+ <SubsOf<T>>::take(&target).0;
			// Slash their deposit from them.
			T::Slashed::on_unbalanced(T::Currency::slash_reserved(&target, deposit).0);

			Self::deposit_event(RawEvent::IdentityKilled(target, deposit));
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use support::{assert_ok, assert_noop, impl_outer_origin, parameter_types, weights::Weight};
	use primitives::H256;
	use system::EnsureSignedBy;
	use balances;
	// The testing primitives are very useful for avoiding having to work with signatures
	// or public keys. `u64` is used as the `AccountId` and no `Signature`s are required.
	use sp_runtime::{
		Perbill, testing::Header, traits::{BlakeTwo256, IdentityLookup},
	};

	impl_outer_origin! {
		pub enum Origin for Test {}
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
	impl system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Call = ();
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
	}
	parameter_types! {
		pub const ExistentialDeposit: u64 = 0;
		pub const TransferFee: u64 = 0;
		pub const CreationFee: u64 = 0;
	}
	impl balances::Trait for Test {
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
		pub const BasicDeposit: u64 = 1;
		pub const FieldDeposit: u64 = 1;
		pub const SubAccountDeposit: u64 = 1;
		pub const MaximumSubAccounts: u32 = 2;
		pub const One: u64 = 1;
		pub const Two: u64 = 2;
	}
	impl Trait for Test {
		type Event = ();
		type Currency = Balances;
		type Slashed = ();
		type BasicDeposit = BasicDeposit;
		type FieldDeposit = FieldDeposit;
		type SubAccountDeposit = SubAccountDeposit;
		type MaximumSubAccounts = MaximumSubAccounts;
		type ForceOrigin = EnsureSignedBy<One, u64>;
		type RegistrarOrigin = EnsureSignedBy<Two, u64>;
	}
	type Balances = balances::Module<Test>;
	type Identity = Module<Test>;

	// This function basically just builds a genesis storage key/value store according to
	// our desired mockup.
	fn new_test_ext() -> runtime_io::TestExternalities {
		let mut t = system::GenesisConfig::default().build_storage::<Test>().unwrap();
		// We use default for brevity, but you can configure as desired if needed.
		balances::GenesisConfig::<Test> {
			balances: vec![
				(1, 10),
				(2, 10),
			],
			vesting: vec![],
		}.assimilate_storage(&mut t).unwrap();
		t.into()
	}
/*
	#[test]
	fn kill_name_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Identity::set_name(Origin::signed(2), b"Dave".to_vec()));
			assert_eq!(Balances::total_balance(&2), 10);
			assert_ok!(Identity::kill_name(Origin::signed(1), 2));
			assert_eq!(Balances::total_balance(&2), 8);
			assert_eq!(<IdentityOf<Test>>::get(2), None);
		});
	}

	#[test]
	fn force_name_should_work() {
		new_test_ext().execute_with(|| {
			assert_noop!(
				Identity::set_name(Origin::signed(2), b"Dr. David Brubeck, III".to_vec()),
				"Identity too long"
			);

			assert_ok!(Identity::set_name(Origin::signed(2), b"Dave".to_vec()));
			assert_eq!(Balances::reserved_balance(&2), 2);
			assert_ok!(Identity::force_name(Origin::signed(1), 2, b"Dr. David Brubeck, III".to_vec()));
			assert_eq!(Balances::reserved_balance(&2), 2);
			assert_eq!(<IdentityOf<Test>>::get(2).unwrap(), (b"Dr. David Brubeck, III".to_vec(), 2));
		});
	}

	#[test]
	fn normal_operation_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Identity::set_name(Origin::signed(1), b"Gav".to_vec()));
			assert_eq!(Balances::reserved_balance(&1), 2);
			assert_eq!(Balances::free_balance(&1), 8);
			assert_eq!(<IdentityOf<Test>>::get(1).unwrap().0, b"Gav".to_vec());

			assert_ok!(Identity::set_name(Origin::signed(1), b"Gavin".to_vec()));
			assert_eq!(Balances::reserved_balance(&1), 2);
			assert_eq!(Balances::free_balance(&1), 8);
			assert_eq!(<IdentityOf<Test>>::get(1).unwrap().0, b"Gavin".to_vec());

			assert_ok!(Identity::clear_name(Origin::signed(1)));
			assert_eq!(Balances::reserved_balance(&1), 0);
			assert_eq!(Balances::free_balance(&1), 10);
		});
	}

	#[test]
	fn error_catching_should_work() {
		new_test_ext().execute_with(|| {
			assert_noop!(Identity::clear_name(Origin::signed(1)), "Not named");

			assert_noop!(Identity::set_name(Origin::signed(3), b"Dave".to_vec()), "not enough free funds");

			assert_noop!(Identity::set_name(Origin::signed(1), b"Ga".to_vec()), "Identity too short");
			assert_noop!(
				Identity::set_name(Origin::signed(1), b"Gavin James Wood, Esquire".to_vec()),
				"Identity too long"
			);
			assert_ok!(Identity::set_name(Origin::signed(1), b"Dave".to_vec()));
			assert_noop!(Identity::kill_name(Origin::signed(2), 1), "bad origin");
			assert_noop!(Identity::force_name(Origin::signed(2), 1, b"Whatever".to_vec()), "bad origin");
		});
	}*/
}
