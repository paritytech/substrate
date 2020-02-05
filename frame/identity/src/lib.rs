// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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
//! each of their fees). Registrar judgements are given as an `enum`, allowing for sophisticated,
//! multi-tier opinions.
//!
//! Some judgements are identified as *sticky*, which means they cannot be removed except by
//! complete removal of the identity, or by the registrar. Judgements are allowed to represent a
//! portion of funds that have been reserved for the registrar.
//!
//! A super-user can remove accounts and in doing so, slash the deposit.
//!
//! All accounts may also have a limited number of sub-accounts which may be specified by the owner;
//! by definition, these have equivalent ownership and each has an individual name.
//!
//! The number of registrars should be limited, and the deposit made sufficiently large, to ensure
//! no state-bloat attack is viable.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! #### For general users
//! * `set_identity` - Set the associated identity of an account; a small deposit is reserved if not
//!   already taken.
//! * `set_subs` - Set the sub-accounts of an identity.
//! * `clear_identity` - Remove an account's associated identity; the deposit is returned.
//! * `request_judgement` - Request a judgement from a registrar, paying a fee.
//! * `cancel_request` - Cancel the previous request for a judgement.
//!
//! #### For registrars
//! * `set_fee` - Set the fee required to be paid for a judgement to be given by the registrar.
//! * `set_fields` - Set the fields that a registrar cares about in their judgements.
//! * `provide_judgement` - Provide a judgement to an identity.
//!
//! #### For super-users
//! * `add_registrar` - Add a new registrar to the system.
//! * `kill_identity` - Forcibly remove the associated identity; the deposit is lost.
//!
//! [`Call`]: ./enum.Call.html
//! [`Trait`]: ./trait.Trait.html

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;
use sp_std::{fmt::Debug, ops::Add, iter::once};
use enumflags2::BitFlags;
use codec::{Encode, Decode};
use sp_runtime::{DispatchResult, RuntimeDebug};
use sp_runtime::traits::{StaticLookup, EnsureOrigin, Zero, AppendZerosInput, Dispatchable};
use frame_support::{
	decl_module, decl_event, decl_storage, ensure, decl_error,
	traits::{Currency, ReservableCurrency, OnUnbalanced, Get},
	weights::SimpleDispatchInfo,
};
use frame_system::{self as system, ensure_signed, ensure_root};

pub mod benchmarking;

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;
type NegativeImbalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::NegativeImbalance;

pub trait Trait: frame_system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;

	/// The currency trait.
	type Currency: ReservableCurrency<Self::AccountId>;

	/// The amount held on deposit for a registered identity.
	type BasicDeposit: Get<BalanceOf<Self>>;

	/// The amount held on deposit per additional field for a registered identity.
	type FieldDeposit: Get<BalanceOf<Self>>;

	/// The amount held on deposit for a registered subaccount. This should account for the fact
	/// that one storage item's value will increase by the size of an account ID, and there will be
	/// another trie item whose value is the size of an account ID plus 32 bytes.
	type SubAccountDeposit: Get<BalanceOf<Self>>;

	/// The maximum number of sub-accounts allowed per identified account.
	type MaxSubAccounts: Get<u32>;

	/// Maximum number of additional fields that may be stored in an ID. Needed to bound the I/O
	/// required to access an identity, but can be pretty high.
	type MaxAdditionalFields: Get<u32>;

	/// What to do with slashed funds.
	type Slashed: OnUnbalanced<NegativeImbalanceOf<Self>>;

	/// The origin which may forcibly set or remove a name. Root can always do this.
	type ForceOrigin: EnsureOrigin<Self::Origin>;

	/// The origin which may add or remove registrars. Root can always do this.
	type RegistrarOrigin: EnsureOrigin<Self::Origin>;
}

/// Either underlying data blob if it is at most 32 bytes, or a hash of it. If the data is greater
/// than 32-bytes then it will be truncated when encoding.
///
/// Can also be `None`.
#[derive(Clone, Eq, PartialEq, RuntimeDebug)]
pub enum Data {
	/// No data here.
	None,
	/// The data is stored directly.
	Raw(Vec<u8>),
	/// Only the Blake2 hash of the data is stored. The preimage of the hash may be retrieved
	/// through some hash-lookup service.
	BlakeTwo256([u8; 32]),
	/// Only the SHA2-256 hash of the data is stored. The preimage of the hash may be retrieved
	/// through some hash-lookup service.
	Sha256([u8; 32]),
	/// Only the Keccak-256 hash of the data is stored. The preimage of the hash may be retrieved
	/// through some hash-lookup service.
	Keccak256([u8; 32]),
	/// Only the SHA3-256 hash of the data is stored. The preimage of the hash may be retrieved
	/// through some hash-lookup service.
	ShaThree256([u8; 32]),
}

impl Decode for Data {
	fn decode<I: codec::Input>(input: &mut I) -> sp_std::result::Result<Self, codec::Error> {
		let b = input.read_byte()?;
		Ok(match b {
			0 => Data::None,
			n @ 1 ..= 33 => {
				let mut r = vec![0u8; n as usize - 1];
				input.read(&mut r[..])?;
				Data::Raw(r)
			}
			34 => Data::BlakeTwo256(<[u8; 32]>::decode(input)?),
			35 => Data::Sha256(<[u8; 32]>::decode(input)?),
			36 => Data::Keccak256(<[u8; 32]>::decode(input)?),
			37 => Data::ShaThree256(<[u8; 32]>::decode(input)?),
			_ => return Err(codec::Error::from("invalid leading byte")),
		})
	}
}

impl Encode for Data {
	fn encode(&self) -> Vec<u8> {
		match self {
			Data::None => vec![0u8; 1],
			Data::Raw(ref x) => {
				let l = x.len().min(32);
				let mut r = vec![l as u8 + 1; l + 1];
				&mut r[1..].copy_from_slice(&x[..l as usize]);
				r
			}
			Data::BlakeTwo256(ref h) => once(34u8).chain(h.iter().cloned()).collect(),
			Data::Sha256(ref h) => once(35u8).chain(h.iter().cloned()).collect(),
			Data::Keccak256(ref h) => once(36u8).chain(h.iter().cloned()).collect(),
			Data::ShaThree256(ref h) => once(37u8).chain(h.iter().cloned()).collect(),
		}
	}
}
impl codec::EncodeLike for Data {}

impl Default for Data {
	fn default() -> Self {
		Self::None
	}
}

/// An identifier for a single name registrar/identity verification service.
pub type RegistrarIndex = u32;

/// An attestation of a registrar over how accurate some `IdentityInfo` is in describing an account.
///
/// NOTE: Registrars may pay little attention to some fields. Registrars may want to make clear
/// which fields their attestation is relevant for by off-chain means.
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
	/// The target is known directly by the registrar and the registrar can fully attest to the
	/// the data's accuracy.
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
	/// Returns `true` if this judgement is indicative of a deposit being currently held. This means
	/// it should not be cleared or replaced except by an operation which utilizes the deposit.
	fn has_deposit(&self) -> bool {
		match self {
			Judgement::FeePaid(_) => true,
			_ => false,
		}
	}

	/// Returns `true` if this judgement is one that should not be generally be replaced outside
	/// of specialized handlers. Examples include "malicious" judgements and deposit-holding
	/// judgements.
	fn is_sticky(&self) -> bool {
		match self {
			Judgement::FeePaid(_) | Judgement::Erroneous => true,
			_ => false,
		}
	}
}

/// The fields that we use to identify the owner of an account with. Each corresponds to a field
/// in the `IdentityInfo` struct.
#[repr(u64)]
#[derive(Encode, Decode, Clone, Copy, PartialEq, Eq, BitFlags, RuntimeDebug)]
pub enum IdentityField {
	Display        = 0b0000000000000000000000000000000000000000000000000000000000000001,
	Legal          = 0b0000000000000000000000000000000000000000000000000000000000000010,
	Web            = 0b0000000000000000000000000000000000000000000000000000000000000100,
	Riot           = 0b0000000000000000000000000000000000000000000000000000000000001000,
	Email          = 0b0000000000000000000000000000000000000000000000000000000000010000,
	PgpFingerprint = 0b0000000000000000000000000000000000000000000000000000000000100000,
	Image          = 0b0000000000000000000000000000000000000000000000000000000001000000,
	Twitter        = 0b0000000000000000000000000000000000000000000000000000000010000000,
}

/// Wrapper type for `BitFlags<IdentityField>` that implements `Codec`.
#[derive(Clone, Copy, PartialEq, Default, RuntimeDebug)]
pub struct IdentityFields(BitFlags<IdentityField>);

impl Eq for IdentityFields {}
impl Encode for IdentityFields {
	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.0.bits().using_encoded(f)
	}
}
impl Decode for IdentityFields {
	fn decode<I: codec::Input>(input: &mut I) -> sp_std::result::Result<Self, codec::Error> {
		let field = u64::decode(input)?;
		Ok(Self(<BitFlags<IdentityField>>::from_bits(field as u64).map_err(|_| "invalid value")?))
	}
}

/// Information concerning the identity of the controller of an account.
///
/// NOTE: This should be stored at the end of the storage item to facilitate the addition of extra
/// fields in a backwards compatible way through a specialized `Decode` impl.
#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug)]
#[cfg_attr(test, derive(Default))]
pub struct IdentityInfo {
	/// Additional fields of the identity that are not catered for with the struct's explicit
	/// fields.
	pub additional: Vec<(Data, Data)>,

	/// A reasonable display name for the controller of the account. This should be whatever it is
	/// that it is typically known as and should not be confusable with other entities, given
	/// reasonable context.
	///
	/// Stored as UTF-8.
	pub display: Data,

	/// The full legal name in the local jurisdiction of the entity. This might be a bit
	/// long-winded.
	///
	/// Stored as UTF-8.
	pub legal: Data,

	/// A representative website held by the controller of the account.
	///
	/// NOTE: `https://` is automatically prepended.
	///
	/// Stored as UTF-8.
	pub web: Data,

	/// The Riot/Matrix handle held by the controller of the account.
	///
	/// Stored as UTF-8.
	pub riot: Data,

	/// The email address of the controller of the account.
	///
	/// Stored as UTF-8.
	pub email: Data,

	/// The PGP/GPG public key of the controller of the account.
	pub pgp_fingerprint: Option<[u8; 20]>,

	/// A graphic image representing the controller of the account. Should be a company,
	/// organization or project logo or a headshot in the case of a human.
	pub image: Data,

	/// The Twitter identity. The leading `@` character may be elided.
	pub twitter: Data,
}

/// Information concerning the identity of the controller of an account.
///
/// NOTE: This is stored separately primarily to facilitate the addition of extra fields in a
/// backwards compatible way through a specialized `Decode` impl.
#[derive(Clone, Encode, Eq, PartialEq, RuntimeDebug)]
pub struct Registration<
	Balance: Encode + Decode + Copy + Clone + Debug + Eq + PartialEq
> {
	/// Judgements from the registrars on this identity. Stored ordered by `RegistrarIndex`. There
	/// may be only a single judgement from each registrar.
	pub judgements: Vec<(RegistrarIndex, Judgement<Balance>)>,

	/// Amount held on deposit for this information.
	pub deposit: Balance,

	/// Information on the identity.
	pub info: IdentityInfo,
}

impl <
	Balance: Encode + Decode + Copy + Clone + Debug + Eq + PartialEq + Zero + Add,
> Registration<Balance> {
	fn total_deposit(&self) -> Balance {
		self.deposit + self.judgements.iter()
			.map(|(_, ref j)| if let Judgement::FeePaid(fee) = j { *fee } else { Zero::zero() })
			.fold(Zero::zero(), |a, i| a + i)
	}
}

impl<
	Balance: Encode + Decode + Copy + Clone + Debug + Eq + PartialEq,
> Decode for Registration<Balance> {
	fn decode<I: codec::Input>(input: &mut I) -> sp_std::result::Result<Self, codec::Error> {
		let (judgements, deposit, info) = Decode::decode(&mut AppendZerosInput::new(input))?;
		Ok(Self { judgements, deposit, info })
	}
}

/// Information concerning a registrar.
#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug)]
pub struct RegistrarInfo<
	Balance: Encode + Decode + Clone + Debug + Eq + PartialEq,
	AccountId: Encode + Decode + Clone + Debug + Eq + PartialEq
> {
	/// The account of the registrar.
	pub account: AccountId,

	/// Amount required to be given to the registrar for them to provide judgement.
	pub fee: Balance,

	/// Relevant fields for this registrar. Registrar judgements are limited to attestations on
	/// these fields.
	pub fields: IdentityFields,
}

decl_storage! {
	trait Store for Module<T: Trait> as Sudo {
		/// Information that is pertinent to identify the entity behind an account.
		pub IdentityOf get(fn identity):
			map hasher(blake2_256) T::AccountId => Option<Registration<BalanceOf<T>>>;

		/// The super-identity of an alternative "sub" identity together with its name, within that
		/// context. If the account is not some other account's sub-identity, then just `None`.
		pub SuperOf get(fn super_of):
			map hasher(blake2_256) T::AccountId => Option<(T::AccountId, Data)>;

		/// Alternative "sub" identities of this account.
		///
		/// The first item is the deposit, the second is a vector of the accounts.
		pub SubsOf get(fn subs):
			map hasher(blake2_256) T::AccountId => (BalanceOf<T>, Vec<T::AccountId>);

		/// The set of registrars. Not expected to get very big as can only be added through a
		/// special origin (likely a council motion).
		///
		/// The index into this can be cast to `RegistrarIndex` to get a valid value.
		pub Registrars get(fn registrars): Vec<Option<RegistrarInfo<BalanceOf<T>, T::AccountId>>>;
	}
}

decl_event!(
	pub enum Event<T> where AccountId = <T as frame_system::Trait>::AccountId, Balance = BalanceOf<T> {
		/// A name was set or reset (which will remove all judgements).
		IdentitySet(AccountId),
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
	}
);

decl_error! {
	/// Error for the identity module.
	pub enum Error for Module<T: Trait> {
		/// Too many subs-accounts.
		TooManySubAccounts,
		/// Account isn't found.
		NotFound,
		/// Account isn't named.
		NotNamed,
		/// Empty index.
		EmptyIndex,
		/// Fee is changed.
		FeeChanged,
		/// No identity found.
		NoIdentity,
		/// Sticky judgement.
		StickyJudgement,
		/// Judgement given.
		JudgementGiven,
		/// Invalid judgement.
		InvalidJudgement,
		/// The index is invalid.
		InvalidIndex,
		/// The target is invalid.
		InvalidTarget,
		/// Too many additional fields.
		TooManyFields,
}
}

decl_module! {
	// Simple declaration of the `Module` type. Lets the macro know what it's working on.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		fn deposit_event() = default;

		/// Add a registrar to the system.
		///
		/// The dispatch origin for this call must be `RegistrarOrigin` or `Root`.
		///
		/// - `account`: the account of the registrar.
		///
		/// Emits `RegistrarAdded` if successful.
		///
		/// # <weight>
		/// - `O(R)` where `R` registrar-count (governance-bounded).
		/// - One storage mutation (codec `O(R)`).
		/// - One event.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(10_000)]
		fn add_registrar(origin, account: T::AccountId) {
			T::RegistrarOrigin::try_origin(origin)
				.map(|_| ())
				.or_else(ensure_root)?;

			let i = <Registrars<T>>::mutate(|r| {
				r.push(Some(RegistrarInfo { account, fee: Zero::zero(), fields: Default::default() }));
				(r.len() - 1) as RegistrarIndex
			});

			Self::deposit_event(RawEvent::RegistrarAdded(i));
		}

		/// Set an account's identity information and reserve the appropriate deposit.
		///
		/// If the account already has identity information, the deposit is taken as part payment
		/// for the new deposit.
		///
		/// The dispatch origin for this call must be _Signed_ and the sender must have a registered
		/// identity.
		///
		/// - `info`: The identity information.
		///
		/// Emits `IdentitySet` if successful.
		///
		/// # <weight>
		/// - `O(X + X' + R)` where `X` additional-field-count (deposit-bounded and code-bounded).
		/// - At most two balance operations.
		/// - One storage mutation (codec-read `O(X' + R)`, codec-write `O(X + R)`).
		/// - One event.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(50_000)]
		fn set_identity(origin, info: IdentityInfo) {
			let sender = ensure_signed(origin)?;
			let extra_fields = info.additional.len() as u32;
			ensure!(extra_fields <= T::MaxAdditionalFields::get(), Error::<T>::TooManyFields);
			let fd = <BalanceOf<T>>::from(extra_fields) * T::FieldDeposit::get();

			let mut id = match <IdentityOf<T>>::get(&sender) {
				Some(mut id) => {
					// Only keep non-positive judgements.
					id.judgements.retain(|j| j.1.is_sticky());
					id.info = info;
					id
				}
				None => Registration { info, judgements: Vec::new(), deposit: Zero::zero() },
			};

			let old_deposit = id.deposit;
			id.deposit = T::BasicDeposit::get() + fd;
			if id.deposit > old_deposit {
				T::Currency::reserve(&sender, id.deposit - old_deposit)?;
			}
			if old_deposit > id.deposit {
				let _ = T::Currency::unreserve(&sender, old_deposit - id.deposit);
			}

			<IdentityOf<T>>::insert(&sender, id);
			Self::deposit_event(RawEvent::IdentitySet(sender));
		}

		/// Set the sub-accounts of the sender.
		///
		/// Payment: Any aggregate balance reserved by previous `set_subs` calls will be returned
		/// and an amount `SubAccountDeposit` will be reserved for each item in `subs`.
		///
		/// The dispatch origin for this call must be _Signed_ and the sender must have a registered
		/// identity.
		///
		/// - `subs`: The identity's sub-accounts.
		///
		/// # <weight>
		/// - `O(S)` where `S` subs-count (hard- and deposit-bounded).
		/// - At most two balance operations.
		/// - At most O(2 * S + 1) storage mutations; codec complexity `O(1 * S + S * 1)`);
		///   one storage-exists.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(50_000)]
		fn set_subs(origin, subs: Vec<(T::AccountId, Data)>) {
			let sender = ensure_signed(origin)?;
			ensure!(<IdentityOf<T>>::exists(&sender), Error::<T>::NotFound);
			ensure!(subs.len() <= T::MaxSubAccounts::get() as usize, Error::<T>::TooManySubAccounts);

			let (old_deposit, old_ids) = <SubsOf<T>>::get(&sender);
			let new_deposit = T::SubAccountDeposit::get() * <BalanceOf<T>>::from(subs.len() as u32);

			if old_deposit < new_deposit {
				T::Currency::reserve(&sender, new_deposit - old_deposit)?;
			}
			// do nothing if they're equal.
			if old_deposit > new_deposit {
				let _ = T::Currency::unreserve(&sender, old_deposit - new_deposit);
			}

			for s in old_ids.iter() {
				<SuperOf<T>>::remove(s);
			}
			let ids = subs.into_iter().map(|(id, name)| {
				<SuperOf<T>>::insert(&id, (sender.clone(), name));
				id
			}).collect::<Vec<_>>();

			if ids.is_empty() {
				<SubsOf<T>>::remove(&sender);
			} else {
				<SubsOf<T>>::insert(&sender, (new_deposit, ids));
			}
		}

		/// Clear an account's identity info and all sub-account and return all deposits.
		///
		/// Payment: All reserved balances on the account are returned.
		///
		/// The dispatch origin for this call must be _Signed_ and the sender must have a registered
		/// identity.
		///
		/// Emits `IdentityCleared` if successful.
		///
		/// # <weight>
		/// - `O(R + S + X)`.
		/// - One balance-reserve operation.
		/// - `S + 2` storage deletions.
		/// - One event.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(50_000)]
		fn clear_identity(origin) {
			let sender = ensure_signed(origin)?;

			let (subs_deposit, sub_ids) = <SubsOf<T>>::take(&sender);
			let deposit = <IdentityOf<T>>::take(&sender).ok_or(Error::<T>::NotNamed)?.total_deposit()
				+ subs_deposit;
			for sub in sub_ids.iter() {
				<SuperOf<T>>::remove(sub);
			}

			let _ = T::Currency::unreserve(&sender, deposit.clone());

			Self::deposit_event(RawEvent::IdentityCleared(sender, deposit));
		}

		/// Request a judgement from a registrar.
		///
		/// Payment: At most `max_fee` will be reserved for payment to the registrar if judgement
		/// given.
		///
		/// The dispatch origin for this call must be _Signed_ and the sender must have a
		/// registered identity.
		///
		/// - `reg_index`: The index of the registrar whose judgement is requested.
		/// - `max_fee`: The maximum fee that may be paid. This should just be auto-populated as:
		///
		/// ```nocompile
		/// Self::registrars(reg_index).uwnrap().fee
		/// ```
		///
		/// Emits `JudgementRequested` if successful.
		///
		/// # <weight>
		/// - `O(R + X)`.
		/// - One balance-reserve operation.
		/// - Storage: 1 read `O(R)`, 1 mutate `O(X + R)`.
		/// - One event.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(50_000)]
		fn request_judgement(origin,
			#[compact] reg_index: RegistrarIndex,
			#[compact] max_fee: BalanceOf<T>,
		) {
			let sender = ensure_signed(origin)?;
			let registrars = <Registrars<T>>::get();
			let registrar = registrars.get(reg_index as usize).and_then(Option::as_ref)
				.ok_or(Error::<T>::EmptyIndex)?;
			ensure!(max_fee >= registrar.fee, Error::<T>::FeeChanged);
			let mut id = <IdentityOf<T>>::get(&sender).ok_or(Error::<T>::NoIdentity)?;

			let item = (reg_index, Judgement::FeePaid(registrar.fee));
			match id.judgements.binary_search_by_key(&reg_index, |x| x.0) {
				Ok(i) => if id.judgements[i].1.is_sticky() {
					Err(Error::<T>::StickyJudgement)?
				} else {
					id.judgements[i] = item
				},
				Err(i) => id.judgements.insert(i, item),
			}

			T::Currency::reserve(&sender, registrar.fee)?;

			<IdentityOf<T>>::insert(&sender, id);

			Self::deposit_event(RawEvent::JudgementRequested(sender, reg_index));
		}

		/// Cancel a previous request.
		///
		/// Payment: A previously reserved deposit is returned on success.
		///
		/// The dispatch origin for this call must be _Signed_ and the sender must have a
		/// registered identity.
		///
		/// - `reg_index`: The index of the registrar whose judgement is no longer requested.
		///
		/// Emits `JudgementUnrequested` if successful.
		///
		/// # <weight>
		/// - `O(R + X)`.
		/// - One balance-reserve operation.
		/// - One storage mutation `O(R + X)`.
		/// - One event.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(50_000)]
		fn cancel_request(origin, reg_index: RegistrarIndex) {
			let sender = ensure_signed(origin)?;
			let mut id = <IdentityOf<T>>::get(&sender).ok_or(Error::<T>::NoIdentity)?;

			let pos = id.judgements.binary_search_by_key(&reg_index, |x| x.0)
				.map_err(|_| Error::<T>::NotFound)?;
			let fee = if let Judgement::FeePaid(fee) = id.judgements.remove(pos).1 {
				fee
			} else {
				Err(Error::<T>::JudgementGiven)?
			};

			let _ = T::Currency::unreserve(&sender, fee);
			<IdentityOf<T>>::insert(&sender, id);

			Self::deposit_event(RawEvent::JudgementUnrequested(sender, reg_index));
		}

		/// Set the fee required for a judgement to be requested from a registrar.
		///
		/// The dispatch origin for this call must be _Signed_ and the sender must be the account
		/// of the registrar whose index is `index`.
		///
		/// - `index`: the index of the registrar whose fee is to be set.
		/// - `fee`: the new fee.
		///
		/// # <weight>
		/// - `O(R)`.
		/// - One storage mutation `O(R)`.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(50_000)]
		fn set_fee(origin,
			#[compact] index: RegistrarIndex,
			#[compact] fee: BalanceOf<T>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			<Registrars<T>>::mutate(|rs|
				rs.get_mut(index as usize)
					.and_then(|x| x.as_mut())
					.and_then(|r| if r.account == who { r.fee = fee; Some(()) } else { None })
					.ok_or_else(|| Error::<T>::InvalidIndex.into())
			)
		}

		/// Change the account associated with a registrar.
		///
		/// The dispatch origin for this call must be _Signed_ and the sender must be the account
		/// of the registrar whose index is `index`.
		///
		/// - `index`: the index of the registrar whose fee is to be set.
		/// - `new`: the new account ID.
		///
		/// # <weight>
		/// - `O(R)`.
		/// - One storage mutation `O(R)`.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(50_000)]
		fn set_account_id(origin,
			#[compact] index: RegistrarIndex,
			new: T::AccountId,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			<Registrars<T>>::mutate(|rs|
				rs.get_mut(index as usize)
					.and_then(|x| x.as_mut())
					.and_then(|r| if r.account == who { r.account = new; Some(()) } else { None })
					.ok_or_else(|| Error::<T>::InvalidIndex.into())
			)
		}

		/// Set the field information for a registrar.
		///
		/// The dispatch origin for this call must be _Signed_ and the sender must be the account
		/// of the registrar whose index is `index`.
		///
		/// - `index`: the index of the registrar whose fee is to be set.
		/// - `fields`: the fields that the registrar concerns themselves with.
		///
		/// # <weight>
		/// - `O(R)`.
		/// - One storage mutation `O(R)`.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(50_000)]
		fn set_fields(origin,
			#[compact] index: RegistrarIndex,
			fields: IdentityFields,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			<Registrars<T>>::mutate(|rs|
				rs.get_mut(index as usize)
					.and_then(|x| x.as_mut())
					.and_then(|r| if r.account == who { r.fields = fields; Some(()) } else { None })
					.ok_or_else(|| Error::<T>::InvalidIndex.into())
			)
		}

		/// Provide a judgement for an account's identity.
		///
		/// The dispatch origin for this call must be _Signed_ and the sender must be the account
		/// of the registrar whose index is `reg_index`.
		///
		/// - `reg_index`: the index of the registrar whose judgement is being made.
		/// - `target`: the account whose identity the judgement is upon. This must be an account
		///   with a registered identity.
		/// - `judgement`: the judgement of the registrar of index `reg_index` about `target`.
		///
		/// Emits `JudgementGiven` if successful.
		///
		/// # <weight>
		/// - `O(R + X)`.
		/// - One balance-transfer operation.
		/// - Up to one account-lookup operation.
		/// - Storage: 1 read `O(R)`, 1 mutate `O(R + X)`.
		/// - One event.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(50_000)]
		fn provide_judgement(origin,
			#[compact] reg_index: RegistrarIndex,
			target: <T::Lookup as StaticLookup>::Source,
			judgement: Judgement<BalanceOf<T>>,
		) {
			let sender = ensure_signed(origin)?;
			let target = T::Lookup::lookup(target)?;
			ensure!(!judgement.has_deposit(), Error::<T>::InvalidJudgement);
			<Registrars<T>>::get()
				.get(reg_index as usize)
				.and_then(Option::as_ref)
				.and_then(|r| if r.account == sender { Some(r) } else { None })
				.ok_or(Error::<T>::InvalidIndex)?;
			let mut id = <IdentityOf<T>>::get(&target).ok_or(Error::<T>::InvalidTarget)?;

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

		/// Remove an account's identity and sub-account information and slash the deposits.
		///
		/// Payment: Reserved balances from `set_subs` and `set_identity` are slashed and handled by
		/// `Slash`. Verification request deposits are not returned; they should be cancelled
		/// manually using `cancel_request`.
		///
		/// The dispatch origin for this call must be _Root_ or match `T::ForceOrigin`.
		///
		/// - `target`: the account whose identity the judgement is upon. This must be an account
		///   with a registered identity.
		///
		/// Emits `IdentityKilled` if successful.
		///
		/// # <weight>
		/// - `O(R + S + X)`.
		/// - One balance-reserve operation.
		/// - `S + 2` storage mutations.
		/// - One event.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(100_000)]
		fn kill_identity(origin, target: <T::Lookup as StaticLookup>::Source) {
			T::ForceOrigin::try_origin(origin)
				.map(|_| ())
				.or_else(ensure_root)?;

			// Figure out who we're meant to be clearing.
			let target = T::Lookup::lookup(target)?;
			// Grab their deposit (and check that they have one).
			let (subs_deposit, sub_ids) = <SubsOf<T>>::take(&target);
			let deposit = <IdentityOf<T>>::take(&target).ok_or(Error::<T>::NotNamed)?.total_deposit()
				+ subs_deposit;
			for sub in sub_ids.iter() {
				<SuperOf<T>>::remove(sub);
			}
			// Slash their deposit from them.
			T::Slashed::on_unbalanced(T::Currency::slash_reserved(&target, deposit).0);

			Self::deposit_event(RawEvent::IdentityKilled(target, deposit));
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use sp_runtime::traits::BadOrigin;
	use frame_support::{
		assert_ok, assert_noop, impl_outer_origin, parameter_types, weights::Weight,
		ord_parameter_types,
	};
	use sp_core::H256;
	use frame_system::EnsureSignedBy;
	// The testing primitives are very useful for avoiding having to work with signatures
	// or public keys. `u64` is used as the `AccountId` and no `Signature`s are required.
	use sp_runtime::{
		Perbill, testing::Header, traits::{BlakeTwo256, IdentityLookup},
	};

	impl_outer_origin! {
		pub enum Origin for Test  where system = frame_system {}
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
		type ModuleToIndex = ();
	}
	parameter_types! {
		pub const ExistentialDeposit: u64 = 0;
		pub const CreationFee: u64 = 0;
	}
	impl pallet_balances::Trait for Test {
		type Balance = u64;
		type OnReapAccount = System;
		type OnNewAccount = ();
		type Event = ();
		type TransferPayment = ();
		type DustRemoval = ();
		type ExistentialDeposit = ExistentialDeposit;
		type CreationFee = CreationFee;
	}
	parameter_types! {
		pub const BasicDeposit: u64 = 10;
		pub const FieldDeposit: u64 = 10;
		pub const SubAccountDeposit: u64 = 10;
		pub const MaxSubAccounts: u32 = 2;
		pub const MaxAdditionalFields: u32 = 2;
	}
	ord_parameter_types! {
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
		type MaxSubAccounts = MaxSubAccounts;
		type MaxAdditionalFields = MaxAdditionalFields;
		type RegistrarOrigin = EnsureSignedBy<One, u64>;
		type ForceOrigin = EnsureSignedBy<Two, u64>;
	}
	type System = frame_system::Module<Test>;
	type Balances = pallet_balances::Module<Test>;
	type Identity = Module<Test>;

	// This function basically just builds a genesis storage key/value store according to
	// our desired mockup.
	fn new_test_ext() -> sp_io::TestExternalities {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		// We use default for brevity, but you can configure as desired if needed.
		pallet_balances::GenesisConfig::<Test> {
			balances: vec![
				(1, 10),
				(2, 10),
				(3, 10),
				(10, 100),
				(20, 100),
				(30, 100),
			],
		}.assimilate_storage(&mut t).unwrap();
		t.into()
	}

	fn ten() -> IdentityInfo {
		IdentityInfo {
			display: Data::Raw(b"ten".to_vec()),
			legal: Data::Raw(b"The Right Ordinal Ten, Esq.".to_vec()),
			.. Default::default()
		}
	}

	#[test]
	fn trailing_zeros_decodes_into_default_data() {
		let encoded = Data::Raw(b"Hello".to_vec()).encode();
		assert!(<(Data, Data)>::decode(&mut &encoded[..]).is_err());
		let input = &mut &encoded[..];
		let (a, b) = <(Data, Data)>::decode(&mut AppendZerosInput::new(input)).unwrap();
		assert_eq!(a, Data::Raw(b"Hello".to_vec()));
		assert_eq!(b, Data::None);
	}

	#[test]
	fn adding_registrar_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Identity::add_registrar(Origin::signed(1), 3));
			assert_ok!(Identity::set_fee(Origin::signed(3), 0, 10));
			let fields = IdentityFields(IdentityField::Display | IdentityField::Legal);
			assert_ok!(Identity::set_fields(Origin::signed(3), 0, fields));
			assert_eq!(Identity::registrars(), vec![
				Some(RegistrarInfo { account: 3, fee: 10, fields })
			]);
		});
	}

	#[test]
	fn registration_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Identity::add_registrar(Origin::signed(1), 3));
			assert_ok!(Identity::set_fee(Origin::signed(3), 0, 10));
			let mut three_fields = ten();
			three_fields.additional.push(Default::default());
			three_fields.additional.push(Default::default());
			three_fields.additional.push(Default::default());
			assert_noop!(
				Identity::set_identity(Origin::signed(10), three_fields),
				Error::<Test>::TooManyFields
			);
			assert_ok!(Identity::set_identity(Origin::signed(10), ten()));
			assert_eq!(Identity::identity(10).unwrap().info, ten());
			assert_eq!(Balances::free_balance(10), 90);
			assert_ok!(Identity::clear_identity(Origin::signed(10)));
			assert_eq!(Balances::free_balance(10), 100);
			assert_noop!(Identity::clear_identity(Origin::signed(10)), Error::<Test>::NotNamed);
		});
	}

	#[test]
	fn uninvited_judgement_should_work() {
		new_test_ext().execute_with(|| {
			assert_noop!(
				Identity::provide_judgement(Origin::signed(3), 0, 10, Judgement::Reasonable),
				Error::<Test>::InvalidIndex
			);

			assert_ok!(Identity::add_registrar(Origin::signed(1), 3));
			assert_noop!(
				Identity::provide_judgement(Origin::signed(3), 0, 10, Judgement::Reasonable),
				Error::<Test>::InvalidTarget
			);

			assert_ok!(Identity::set_identity(Origin::signed(10), ten()));
			assert_noop!(
				Identity::provide_judgement(Origin::signed(10), 0, 10, Judgement::Reasonable),
				Error::<Test>::InvalidIndex
			);
			assert_noop!(
				Identity::provide_judgement(Origin::signed(3), 0, 10, Judgement::FeePaid(1)),
				Error::<Test>::InvalidJudgement
			);

			assert_ok!(Identity::provide_judgement(Origin::signed(3), 0, 10, Judgement::Reasonable));
			assert_eq!(Identity::identity(10).unwrap().judgements, vec![(0, Judgement::Reasonable)]);
		});
	}

	#[test]
	fn clearing_judgement_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Identity::add_registrar(Origin::signed(1), 3));
			assert_ok!(Identity::set_identity(Origin::signed(10), ten()));
			assert_ok!(Identity::provide_judgement(Origin::signed(3), 0, 10, Judgement::Reasonable));
			assert_ok!(Identity::clear_identity(Origin::signed(10)));
			assert_eq!(Identity::identity(10), None);
		});
	}

	#[test]
	fn killing_slashing_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Identity::set_identity(Origin::signed(10), ten()));
			assert_noop!(Identity::kill_identity(Origin::signed(1), 10), BadOrigin);
			assert_ok!(Identity::kill_identity(Origin::signed(2), 10));
			assert_eq!(Identity::identity(10), None);
			assert_eq!(Balances::free_balance(10), 90);
			assert_noop!(Identity::kill_identity(Origin::signed(2), 10), Error::<Test>::NotNamed);
		});
	}

	#[test]
	fn setting_subaccounts_should_work() {
		new_test_ext().execute_with(|| {
			let mut subs = vec![(20, Data::Raw(vec![40; 1]))];
			assert_noop!(Identity::set_subs(Origin::signed(10), subs.clone()), Error::<Test>::NotFound);

			assert_ok!(Identity::set_identity(Origin::signed(10), ten()));
			assert_ok!(Identity::set_subs(Origin::signed(10), subs.clone()));
			assert_eq!(Balances::free_balance(10), 80);
			assert_eq!(Identity::subs(10), (10, vec![20]));
			assert_eq!(Identity::super_of(20), Some((10, Data::Raw(vec![40; 1]))));

			// push another item and re-set it.
			subs.push((30, Data::Raw(vec![50; 1])));
			assert_ok!(Identity::set_subs(Origin::signed(10), subs.clone()));
			assert_eq!(Balances::free_balance(10), 70);
			assert_eq!(Identity::subs(10), (20, vec![20, 30]));
			assert_eq!(Identity::super_of(20), Some((10, Data::Raw(vec![40; 1]))));
			assert_eq!(Identity::super_of(30), Some((10, Data::Raw(vec![50; 1]))));

			// switch out one of the items and re-set.
			subs[0] = (40, Data::Raw(vec![60; 1]));
			assert_ok!(Identity::set_subs(Origin::signed(10), subs.clone()));
			assert_eq!(Balances::free_balance(10), 70); // no change in the balance
			assert_eq!(Identity::subs(10), (20, vec![40, 30]));
			assert_eq!(Identity::super_of(20), None);
			assert_eq!(Identity::super_of(30), Some((10, Data::Raw(vec![50; 1]))));
			assert_eq!(Identity::super_of(40), Some((10, Data::Raw(vec![60; 1]))));

			// clear
			assert_ok!(Identity::set_subs(Origin::signed(10), vec![]));
			assert_eq!(Balances::free_balance(10), 90);
			assert_eq!(Identity::subs(10), (0, vec![]));
			assert_eq!(Identity::super_of(30), None);
			assert_eq!(Identity::super_of(40), None);

			subs.push((20, Data::Raw(vec![40; 1])));
			assert_noop!(Identity::set_subs(Origin::signed(10), subs.clone()), Error::<Test>::TooManySubAccounts);
		});
	}

	#[test]
	fn clearing_account_should_remove_subaccounts_and_refund() {
		new_test_ext().execute_with(|| {
			assert_ok!(Identity::set_identity(Origin::signed(10), ten()));
			assert_ok!(Identity::set_subs(Origin::signed(10), vec![(20, Data::Raw(vec![40; 1]))]));
			assert_ok!(Identity::clear_identity(Origin::signed(10)));
			assert_eq!(Balances::free_balance(10), 100);
			assert!(Identity::super_of(20).is_none());
		});
	}

	#[test]
	fn killing_account_should_remove_subaccounts_and_not_refund() {
		new_test_ext().execute_with(|| {
			assert_ok!(Identity::set_identity(Origin::signed(10), ten()));
			assert_ok!(Identity::set_subs(Origin::signed(10), vec![(20, Data::Raw(vec![40; 1]))]));
			assert_ok!(Identity::kill_identity(Origin::ROOT, 10));
			assert_eq!(Balances::free_balance(10), 80);
			assert!(Identity::super_of(20).is_none());
		});
	}

	#[test]
	fn cancelling_requested_judgement_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Identity::add_registrar(Origin::signed(1), 3));
			assert_ok!(Identity::set_fee(Origin::signed(3), 0, 10));
			assert_noop!(Identity::cancel_request(Origin::signed(10), 0), Error::<Test>::NoIdentity);
			assert_ok!(Identity::set_identity(Origin::signed(10), ten()));
			assert_ok!(Identity::request_judgement(Origin::signed(10), 0, 10));
			assert_ok!(Identity::cancel_request(Origin::signed(10), 0));
			assert_eq!(Balances::free_balance(10), 90);
			assert_noop!(Identity::cancel_request(Origin::signed(10), 0), Error::<Test>::NotFound);

			assert_ok!(Identity::provide_judgement(Origin::signed(3), 0, 10, Judgement::Reasonable));
			assert_noop!(Identity::cancel_request(Origin::signed(10), 0), Error::<Test>::JudgementGiven);
		});
	}

	#[test]
	fn requesting_judgement_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Identity::add_registrar(Origin::signed(1), 3));
			assert_ok!(Identity::set_fee(Origin::signed(3), 0, 10));
			assert_ok!(Identity::set_identity(Origin::signed(10), ten()));
			assert_noop!(Identity::request_judgement(Origin::signed(10), 0, 9), Error::<Test>::FeeChanged);
			assert_ok!(Identity::request_judgement(Origin::signed(10), 0, 10));
			// 10 for the judgement request, 10 for the identity.
			assert_eq!(Balances::free_balance(10), 80);

			// Re-requesting won't work as we already paid.
			assert_noop!(Identity::request_judgement(Origin::signed(10), 0, 10), Error::<Test>::StickyJudgement);
			assert_ok!(Identity::provide_judgement(Origin::signed(3), 0, 10, Judgement::Erroneous));
			// Registrar got their payment now.
			assert_eq!(Balances::free_balance(3), 20);

			// Re-requesting still won't work as it's erroneous.
			assert_noop!(Identity::request_judgement(Origin::signed(10), 0, 10), Error::<Test>::StickyJudgement);

			// Requesting from a second registrar still works.
			assert_ok!(Identity::add_registrar(Origin::signed(1), 4));
			assert_ok!(Identity::request_judgement(Origin::signed(10), 1, 10));

			// Re-requesting after the judgement has been reduced works.
			assert_ok!(Identity::provide_judgement(Origin::signed(3), 0, 10, Judgement::OutOfDate));
			assert_ok!(Identity::request_judgement(Origin::signed(10), 0, 10));
		});
	}

	#[test]
	fn field_deposit_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Identity::add_registrar(Origin::signed(1), 3));
			assert_ok!(Identity::set_fee(Origin::signed(3), 0, 10));
			assert_ok!(Identity::set_identity(Origin::signed(10), IdentityInfo {
				additional: vec![
					(Data::Raw(b"number".to_vec()), Data::Raw(10u32.encode())),
					(Data::Raw(b"text".to_vec()), Data::Raw(b"10".to_vec())),
				], .. Default::default()
			}));
			assert_eq!(Balances::free_balance(10), 70);
		});
	}

	#[test]
	fn setting_account_id_should_work() {
		new_test_ext().execute_with(|| {
			assert_ok!(Identity::add_registrar(Origin::signed(1), 3));
			// account 4 cannot change the first registrar's identity since it's owned by 3.
			assert_noop!(Identity::set_account_id(Origin::signed(4), 0, 3), Error::<Test>::InvalidIndex);
			// account 3 can, because that's the registrar's current account.
			assert_ok!(Identity::set_account_id(Origin::signed(3), 0, 4));
			// account 4 can now, because that's their new ID.
			assert_ok!(Identity::set_account_id(Origin::signed(4), 0, 3));
		});
	}
}
