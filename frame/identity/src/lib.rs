// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! # Identity Module
//!
//! - [`Config`]
//! - [`Call`]
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
//! * `clear_identity` - Remove an account's associated identity; the deposit is returned.
//! * `request_judgement` - Request a judgement from a registrar, paying a fee.
//! * `cancel_request` - Cancel the previous request for a judgement.
//!
//! #### For general users with sub-identities
//! * `set_subs` - Set the sub-accounts of an identity.
//! * `add_sub` - Add a sub-identity to an identity.
//! * `remove_sub` - Remove a sub-identity of an identity.
//! * `rename_sub` - Rename a sub-identity of an identity.
//! * `quit_sub` - Remove a sub-identity of an identity (called by the sub-identity).
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
//! [`Config`]: ./trait.Config.html

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod tests;
mod benchmarking;
pub mod weights;

use sp_std::prelude::*;
use sp_std::{fmt::Debug, ops::Add, iter::once};
use enumflags2::BitFlags;
use codec::{Encode, Decode};
use sp_runtime::{DispatchError, RuntimeDebug, DispatchResult};
use sp_runtime::traits::{StaticLookup, Zero, AppendZerosInput, Saturating};
use frame_support::{
	decl_module, decl_event, decl_storage, ensure, decl_error,
	dispatch::DispatchResultWithPostInfo,
	traits::{Currency, ReservableCurrency, OnUnbalanced, Get, BalanceStatus, EnsureOrigin},
};
use frame_system::ensure_signed;
pub use weights::WeightInfo;

type BalanceOf<T> = <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
type NegativeImbalanceOf<T> = <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::NegativeImbalance;

pub trait Config: frame_system::Config {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Config>::Event>;

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

	/// Maxmimum number of registrars allowed in the system. Needed to bound the complexity
	/// of, e.g., updating judgements.
	type MaxRegistrars: Get<u32>;

	/// What to do with slashed funds.
	type Slashed: OnUnbalanced<NegativeImbalanceOf<Self>>;

	/// The origin which may forcibly set or remove a name. Root can always do this.
	type ForceOrigin: EnsureOrigin<Self::Origin>;

	/// The origin which may add or remove registrars. Root can always do this.
	type RegistrarOrigin: EnsureOrigin<Self::Origin>;

	/// Weight information for extrinsics in this pallet.
	type WeightInfo: WeightInfo;
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
	trait Store for Module<T: Config> as Identity {
		/// Information that is pertinent to identify the entity behind an account.
		///
		/// TWOX-NOTE: OK ― `AccountId` is a secure hash.
		pub IdentityOf get(fn identity):
			map hasher(twox_64_concat) T::AccountId => Option<Registration<BalanceOf<T>>>;

		/// The super-identity of an alternative "sub" identity together with its name, within that
		/// context. If the account is not some other account's sub-identity, then just `None`.
		pub SuperOf get(fn super_of):
			map hasher(blake2_128_concat) T::AccountId => Option<(T::AccountId, Data)>;

		/// Alternative "sub" identities of this account.
		///
		/// The first item is the deposit, the second is a vector of the accounts.
		///
		/// TWOX-NOTE: OK ― `AccountId` is a secure hash.
		pub SubsOf get(fn subs_of):
			map hasher(twox_64_concat) T::AccountId => (BalanceOf<T>, Vec<T::AccountId>);

		/// The set of registrars. Not expected to get very big as can only be added through a
		/// special origin (likely a council motion).
		///
		/// The index into this can be cast to `RegistrarIndex` to get a valid value.
		pub Registrars get(fn registrars): Vec<Option<RegistrarInfo<BalanceOf<T>, T::AccountId>>>;
	}
}

decl_event!(
	pub enum Event<T> where AccountId = <T as frame_system::Config>::AccountId, Balance = BalanceOf<T> {
		/// A name was set or reset (which will remove all judgements). \[who\]
		IdentitySet(AccountId),
		/// A name was cleared, and the given balance returned. \[who, deposit\]
		IdentityCleared(AccountId, Balance),
		/// A name was removed and the given balance slashed. \[who, deposit\]
		IdentityKilled(AccountId, Balance),
		/// A judgement was asked from a registrar. \[who, registrar_index\]
		JudgementRequested(AccountId, RegistrarIndex),
		/// A judgement request was retracted. \[who, registrar_index\]
		JudgementUnrequested(AccountId, RegistrarIndex),
		/// A judgement was given by a registrar. \[target, registrar_index\]
		JudgementGiven(AccountId, RegistrarIndex),
		/// A registrar was added. \[registrar_index\]
		RegistrarAdded(RegistrarIndex),
		/// A sub-identity was added to an identity and the deposit paid. \[sub, main, deposit\]
		SubIdentityAdded(AccountId, AccountId, Balance),
		/// A sub-identity was removed from an identity and the deposit freed.
		/// \[sub, main, deposit\]
		SubIdentityRemoved(AccountId, AccountId, Balance),
		/// A sub-identity was cleared, and the given deposit repatriated from the
		/// main identity account to the sub-identity account. \[sub, main, deposit\]
		SubIdentityRevoked(AccountId, AccountId, Balance),
	}
);

decl_error! {
	/// Error for the identity module.
	pub enum Error for Module<T: Config> {
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
		/// Maximum amount of registrars reached. Cannot add any more.
		TooManyRegistrars,
		/// Account ID is already named.
		AlreadyClaimed,
		/// Sender is not a sub-account.
		NotSub,
		/// Sub-account isn't owned by sender.
		NotOwned
	}
}

decl_module! {
	/// Identity module declaration.
	pub struct Module<T: Config> for enum Call where origin: T::Origin {
		/// The amount held on deposit for a registered identity.
		const BasicDeposit: BalanceOf<T> = T::BasicDeposit::get();

		/// The amount held on deposit per additional field for a registered identity.
		const FieldDeposit: BalanceOf<T> = T::FieldDeposit::get();

		/// The amount held on deposit for a registered subaccount. This should account for the fact
		/// that one storage item's value will increase by the size of an account ID, and there will be
		/// another trie item whose value is the size of an account ID plus 32 bytes.
		const SubAccountDeposit: BalanceOf<T> = T::SubAccountDeposit::get();

		/// The maximum number of sub-accounts allowed per identified account.
		const MaxSubAccounts: u32 = T::MaxSubAccounts::get();

		/// Maximum number of additional fields that may be stored in an ID. Needed to bound the I/O
		/// required to access an identity, but can be pretty high.
		const MaxAdditionalFields: u32 = T::MaxAdditionalFields::get();

		/// Maxmimum number of registrars allowed in the system. Needed to bound the complexity
		/// of, e.g., updating judgements.
		const MaxRegistrars: u32 = T::MaxRegistrars::get();

		type Error = Error<T>;

		fn deposit_event() = default;

		/// Add a registrar to the system.
		///
		/// The dispatch origin for this call must be `T::RegistrarOrigin`.
		///
		/// - `account`: the account of the registrar.
		///
		/// Emits `RegistrarAdded` if successful.
		///
		/// # <weight>
		/// - `O(R)` where `R` registrar-count (governance-bounded and code-bounded).
		/// - One storage mutation (codec `O(R)`).
		/// - One event.
		/// # </weight>
		#[weight = T::WeightInfo::add_registrar(T::MaxRegistrars::get()) ]
		fn add_registrar(origin, account: T::AccountId) -> DispatchResultWithPostInfo {
			T::RegistrarOrigin::ensure_origin(origin)?;

			let (i, registrar_count) = <Registrars<T>>::try_mutate(
				|registrars| -> Result<(RegistrarIndex, usize), DispatchError> {
					ensure!(registrars.len() < T::MaxRegistrars::get() as usize, Error::<T>::TooManyRegistrars);
					registrars.push(Some(RegistrarInfo {
						account, fee: Zero::zero(), fields: Default::default()
					}));
					Ok(((registrars.len() - 1) as RegistrarIndex, registrars.len()))
				}
			)?;

			Self::deposit_event(RawEvent::RegistrarAdded(i));

			Ok(Some(T::WeightInfo::add_registrar(registrar_count as u32)).into())
		}

		/// Set an account's identity information and reserve the appropriate deposit.
		///
		/// If the account already has identity information, the deposit is taken as part payment
		/// for the new deposit.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// - `info`: The identity information.
		///
		/// Emits `IdentitySet` if successful.
		///
		/// # <weight>
		/// - `O(X + X' + R)`
		///   - where `X` additional-field-count (deposit-bounded and code-bounded)
		///   - where `R` judgements-count (registrar-count-bounded)
		/// - One balance reserve operation.
		/// - One storage mutation (codec-read `O(X' + R)`, codec-write `O(X + R)`).
		/// - One event.
		/// # </weight>
		#[weight =  T::WeightInfo::set_identity(
			T::MaxRegistrars::get().into(), // R
			T::MaxAdditionalFields::get().into(), // X
		)]
		fn set_identity(origin, info: IdentityInfo) -> DispatchResultWithPostInfo {
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
				let err_amount = T::Currency::unreserve(&sender, old_deposit - id.deposit);
				debug_assert!(err_amount.is_zero());
			}

			let judgements = id.judgements.len();
			<IdentityOf<T>>::insert(&sender, id);
			Self::deposit_event(RawEvent::IdentitySet(sender));

			Ok(Some(T::WeightInfo::set_identity(
				judgements as u32, // R
				extra_fields // X
			)).into())
		}

		/// Set the sub-accounts of the sender.
		///
		/// Payment: Any aggregate balance reserved by previous `set_subs` calls will be returned
		/// and an amount `SubAccountDeposit` will be reserved for each item in `subs`.
		///
		/// The dispatch origin for this call must be _Signed_ and the sender must have a registered
		/// identity.
		///
		/// - `subs`: The identity's (new) sub-accounts.
		///
		/// # <weight>
		/// - `O(P + S)`
		///   - where `P` old-subs-count (hard- and deposit-bounded).
		///   - where `S` subs-count (hard- and deposit-bounded).
		/// - At most one balance operations.
		/// - DB:
		///   - `P + S` storage mutations (codec complexity `O(1)`)
		///   - One storage read (codec complexity `O(P)`).
		///   - One storage write (codec complexity `O(S)`).
		///   - One storage-exists (`IdentityOf::contains_key`).
		/// # </weight>
		// TODO: This whole extrinsic screams "not optimized". For example we could
		// filter any overlap between new and old subs, and avoid reading/writing
		// to those values... We could also ideally avoid needing to write to
		// N storage items for N sub accounts. Right now the weight on this function
		// is a large overestimate due to the fact that it could potentially write
		// to 2 x T::MaxSubAccounts::get().
		#[weight = T::WeightInfo::set_subs_old(T::MaxSubAccounts::get()) // P: Assume max sub accounts removed.
			.saturating_add(T::WeightInfo::set_subs_new(subs.len() as u32)) // S: Assume all subs are new.
		]
		fn set_subs(origin, subs: Vec<(T::AccountId, Data)>) -> DispatchResultWithPostInfo {
			let sender = ensure_signed(origin)?;
			ensure!(<IdentityOf<T>>::contains_key(&sender), Error::<T>::NotFound);
			ensure!(subs.len() <= T::MaxSubAccounts::get() as usize, Error::<T>::TooManySubAccounts);

			let (old_deposit, old_ids) = <SubsOf<T>>::get(&sender);
			let new_deposit = T::SubAccountDeposit::get() * <BalanceOf<T>>::from(subs.len() as u32);

			let not_other_sub = subs.iter().filter_map(|i| SuperOf::<T>::get(&i.0)).all(|i| &i.0 == &sender);
			ensure!(not_other_sub, Error::<T>::AlreadyClaimed);

			if old_deposit < new_deposit {
				T::Currency::reserve(&sender, new_deposit - old_deposit)?;
			} else if old_deposit > new_deposit {
				let err_amount = T::Currency::unreserve(&sender, old_deposit - new_deposit);
				debug_assert!(err_amount.is_zero());
			}
			// do nothing if they're equal.

			for s in old_ids.iter() {
				<SuperOf<T>>::remove(s);
			}
			let ids = subs.into_iter().map(|(id, name)| {
				<SuperOf<T>>::insert(&id, (sender.clone(), name));
				id
			}).collect::<Vec<_>>();
			let new_subs = ids.len();

			if ids.is_empty() {
				<SubsOf<T>>::remove(&sender);
			} else {
				<SubsOf<T>>::insert(&sender, (new_deposit, ids));
			}

			Ok(Some(
				T::WeightInfo::set_subs_old(old_ids.len() as u32) // P: Real number of old accounts removed.
				.saturating_add(T::WeightInfo::set_subs_new(new_subs as u32)) // S: New subs added.
			).into())
		}

		/// Clear an account's identity info and all sub-accounts and return all deposits.
		///
		/// Payment: All reserved balances on the account are returned.
		///
		/// The dispatch origin for this call must be _Signed_ and the sender must have a registered
		/// identity.
		///
		/// Emits `IdentityCleared` if successful.
		///
		/// # <weight>
		/// - `O(R + S + X)`
		///   - where `R` registrar-count (governance-bounded).
		///   - where `S` subs-count (hard- and deposit-bounded).
		///   - where `X` additional-field-count (deposit-bounded and code-bounded).
		/// - One balance-unreserve operation.
		/// - `2` storage reads and `S + 2` storage deletions.
		/// - One event.
		/// # </weight>
		#[weight = T::WeightInfo::clear_identity(
			T::MaxRegistrars::get().into(), // R
			T::MaxSubAccounts::get().into(), // S
			T::MaxAdditionalFields::get().into(), // X
		)]
		fn clear_identity(origin) -> DispatchResultWithPostInfo {
			let sender = ensure_signed(origin)?;

			let (subs_deposit, sub_ids) = <SubsOf<T>>::take(&sender);
			let id = <IdentityOf<T>>::take(&sender).ok_or(Error::<T>::NotNamed)?;
			let deposit = id.total_deposit() + subs_deposit;
			for sub in sub_ids.iter() {
				<SuperOf<T>>::remove(sub);
			}

			let err_amount = T::Currency::unreserve(&sender, deposit.clone());
			debug_assert!(err_amount.is_zero());

			Self::deposit_event(RawEvent::IdentityCleared(sender, deposit));

			Ok(Some(T::WeightInfo::clear_identity(
				id.judgements.len() as u32, // R
				sub_ids.len() as u32, // S
				id.info.additional.len() as u32 // X
			)).into())
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
		/// Self::registrars().get(reg_index).unwrap().fee
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
		#[weight = T::WeightInfo::request_judgement(
			T::MaxRegistrars::get().into(), // R
			T::MaxAdditionalFields::get().into(), // X
		)]
		fn request_judgement(origin,
			#[compact] reg_index: RegistrarIndex,
			#[compact] max_fee: BalanceOf<T>,
		) -> DispatchResultWithPostInfo {
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

			let judgements = id.judgements.len();
			let extra_fields = id.info.additional.len();
			<IdentityOf<T>>::insert(&sender, id);

			Self::deposit_event(RawEvent::JudgementRequested(sender, reg_index));

			Ok(Some(T::WeightInfo::request_judgement(
				judgements as u32,
				extra_fields as u32,
			)).into())
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
		/// - One event
		/// # </weight>
		#[weight = T::WeightInfo::cancel_request(
			T::MaxRegistrars::get().into(), // R
			T::MaxAdditionalFields::get().into(), // X
		)]
		fn cancel_request(origin, reg_index: RegistrarIndex) -> DispatchResultWithPostInfo {
			let sender = ensure_signed(origin)?;
			let mut id = <IdentityOf<T>>::get(&sender).ok_or(Error::<T>::NoIdentity)?;

			let pos = id.judgements.binary_search_by_key(&reg_index, |x| x.0)
				.map_err(|_| Error::<T>::NotFound)?;
			let fee = if let Judgement::FeePaid(fee) = id.judgements.remove(pos).1 {
				fee
			} else {
				Err(Error::<T>::JudgementGiven)?
			};

			let err_amount = T::Currency::unreserve(&sender, fee);
			debug_assert!(err_amount.is_zero());
			let judgements = id.judgements.len();
			let extra_fields = id.info.additional.len();
			<IdentityOf<T>>::insert(&sender, id);

			Self::deposit_event(RawEvent::JudgementUnrequested(sender, reg_index));

			Ok(Some(T::WeightInfo::cancel_request(
				judgements as u32,
				extra_fields as u32
			)).into())
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
		/// - Benchmark: 7.315 + R * 0.329 µs (min squares analysis)
		/// # </weight>
		#[weight = T::WeightInfo::set_fee(T::MaxRegistrars::get())] // R
		fn set_fee(origin,
			#[compact] index: RegistrarIndex,
			#[compact] fee: BalanceOf<T>,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			let registrars = <Registrars<T>>::mutate(|rs| -> Result<usize, DispatchError> {
				rs.get_mut(index as usize)
					.and_then(|x| x.as_mut())
					.and_then(|r| if r.account == who { r.fee = fee; Some(()) } else { None })
					.ok_or_else(|| DispatchError::from(Error::<T>::InvalidIndex))?;
				Ok(rs.len())
			})?;
			Ok(Some(T::WeightInfo::set_fee(registrars as u32)).into()) // R
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
		/// - Benchmark: 8.823 + R * 0.32 µs (min squares analysis)
		/// # </weight>
		#[weight = T::WeightInfo::set_account_id(T::MaxRegistrars::get())] // R
		fn set_account_id(origin,
			#[compact] index: RegistrarIndex,
			new: T::AccountId,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			let registrars = <Registrars<T>>::mutate(|rs| -> Result<usize, DispatchError> {
				rs.get_mut(index as usize)
					.and_then(|x| x.as_mut())
					.and_then(|r| if r.account == who { r.account = new; Some(()) } else { None })
					.ok_or_else(|| DispatchError::from(Error::<T>::InvalidIndex))?;
				Ok(rs.len())
			})?;
			Ok(Some(T::WeightInfo::set_account_id(registrars as u32)).into()) // R
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
		/// - Benchmark: 7.464 + R * 0.325 µs (min squares analysis)
		/// # </weight>
		#[weight = T::WeightInfo::set_fields(T::MaxRegistrars::get())] // R
		fn set_fields(origin,
			#[compact] index: RegistrarIndex,
			fields: IdentityFields,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			let registrars = <Registrars<T>>::mutate(|rs| -> Result<usize, DispatchError> {
				rs.get_mut(index as usize)
					.and_then(|x| x.as_mut())
					.and_then(|r| if r.account == who { r.fields = fields; Some(()) } else { None })
					.ok_or_else(|| DispatchError::from(Error::<T>::InvalidIndex))?;
				Ok(rs.len())
			})?;
			Ok(Some(T::WeightInfo::set_fields(
				registrars as u32 // R
			)).into())
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
		#[weight = T::WeightInfo::provide_judgement(
			T::MaxRegistrars::get().into(), // R
			T::MaxAdditionalFields::get().into(), // X
		)]
		fn provide_judgement(origin,
			#[compact] reg_index: RegistrarIndex,
			target: <T::Lookup as StaticLookup>::Source,
			judgement: Judgement<BalanceOf<T>>,
		) -> DispatchResultWithPostInfo {
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
						let _ = T::Currency::repatriate_reserved(&target, &sender, fee, BalanceStatus::Free);
					}
					id.judgements[position] = item
				}
				Err(position) => id.judgements.insert(position, item),
			}

			let judgements = id.judgements.len();
			let extra_fields = id.info.additional.len();
			<IdentityOf<T>>::insert(&target, id);
			Self::deposit_event(RawEvent::JudgementGiven(target, reg_index));

			Ok(Some(T::WeightInfo::provide_judgement(
				judgements as u32,
				extra_fields as u32,
			)).into())
		}

		/// Remove an account's identity and sub-account information and slash the deposits.
		///
		/// Payment: Reserved balances from `set_subs` and `set_identity` are slashed and handled by
		/// `Slash`. Verification request deposits are not returned; they should be cancelled
		/// manually using `cancel_request`.
		///
		/// The dispatch origin for this call must match `T::ForceOrigin`.
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
		#[weight = T::WeightInfo::kill_identity(
			T::MaxRegistrars::get().into(), // R
			T::MaxSubAccounts::get().into(), // S
			T::MaxAdditionalFields::get().into(), // X
		)]
		fn kill_identity(origin, target: <T::Lookup as StaticLookup>::Source) -> DispatchResultWithPostInfo {
			T::ForceOrigin::ensure_origin(origin)?;

			// Figure out who we're meant to be clearing.
			let target = T::Lookup::lookup(target)?;
			// Grab their deposit (and check that they have one).
			let (subs_deposit, sub_ids) = <SubsOf<T>>::take(&target);
			let id = <IdentityOf<T>>::take(&target).ok_or(Error::<T>::NotNamed)?;
			let deposit = id.total_deposit() + subs_deposit;
			for sub in sub_ids.iter() {
				<SuperOf<T>>::remove(sub);
			}
			// Slash their deposit from them.
			T::Slashed::on_unbalanced(T::Currency::slash_reserved(&target, deposit).0);

			Self::deposit_event(RawEvent::IdentityKilled(target, deposit));

			Ok(Some(T::WeightInfo::kill_identity(
				id.judgements.len() as u32, // R
				sub_ids.len() as u32, // S
				id.info.additional.len() as u32 // X
			)).into())
		}

		/// Add the given account to the sender's subs.
		///
		/// Payment: Balance reserved by a previous `set_subs` call for one sub will be repatriated
		/// to the sender.
		///
		/// The dispatch origin for this call must be _Signed_ and the sender must have a registered
		/// sub identity of `sub`.
		#[weight = T::WeightInfo::add_sub(T::MaxSubAccounts::get())]
		fn add_sub(origin, sub: <T::Lookup as StaticLookup>::Source, data: Data) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let sub = T::Lookup::lookup(sub)?;
			ensure!(IdentityOf::<T>::contains_key(&sender), Error::<T>::NoIdentity);

			// Check if it's already claimed as sub-identity.
			ensure!(!SuperOf::<T>::contains_key(&sub), Error::<T>::AlreadyClaimed);

			SubsOf::<T>::try_mutate(&sender, |(ref mut subs_deposit, ref mut sub_ids)| {
				// Ensure there is space and that the deposit is paid.
				ensure!(sub_ids.len() < T::MaxSubAccounts::get() as usize, Error::<T>::TooManySubAccounts);
				let deposit = T::SubAccountDeposit::get();
				T::Currency::reserve(&sender, deposit)?;

				SuperOf::<T>::insert(&sub, (sender.clone(), data));
				sub_ids.push(sub.clone());
				*subs_deposit = subs_deposit.saturating_add(deposit);

				Self::deposit_event(RawEvent::SubIdentityAdded(sub, sender.clone(), deposit));
				Ok(())
			})
		}

		/// Alter the associated name of the given sub-account.
		///
		/// The dispatch origin for this call must be _Signed_ and the sender must have a registered
		/// sub identity of `sub`.
		#[weight = T::WeightInfo::rename_sub(T::MaxSubAccounts::get())]
		fn rename_sub(origin, sub: <T::Lookup as StaticLookup>::Source, data: Data) {
			let sender = ensure_signed(origin)?;
			let sub = T::Lookup::lookup(sub)?;
			ensure!(IdentityOf::<T>::contains_key(&sender), Error::<T>::NoIdentity);
			ensure!(SuperOf::<T>::get(&sub).map_or(false, |x| x.0 == sender), Error::<T>::NotOwned);
			SuperOf::<T>::insert(&sub, (sender, data));
		}

		/// Remove the given account from the sender's subs.
		///
		/// Payment: Balance reserved by a previous `set_subs` call for one sub will be repatriated
		/// to the sender.
		///
		/// The dispatch origin for this call must be _Signed_ and the sender must have a registered
		/// sub identity of `sub`.
		#[weight = T::WeightInfo::remove_sub(T::MaxSubAccounts::get())]
		fn remove_sub(origin, sub: <T::Lookup as StaticLookup>::Source) {
			let sender = ensure_signed(origin)?;
			ensure!(IdentityOf::<T>::contains_key(&sender), Error::<T>::NoIdentity);
			let sub = T::Lookup::lookup(sub)?;
			let (sup, _) = SuperOf::<T>::get(&sub).ok_or(Error::<T>::NotSub)?;
			ensure!(sup == sender, Error::<T>::NotOwned);
			SuperOf::<T>::remove(&sub);
			SubsOf::<T>::mutate(&sup, |(ref mut subs_deposit, ref mut sub_ids)| {
				sub_ids.retain(|x| x != &sub);
				let deposit = T::SubAccountDeposit::get().min(*subs_deposit);
				*subs_deposit -= deposit;
				let err_amount = T::Currency::unreserve(&sender, deposit);
				debug_assert!(err_amount.is_zero());
				Self::deposit_event(RawEvent::SubIdentityRemoved(sub, sender, deposit));
			});
		}

		/// Remove the sender as a sub-account.
		///
		/// Payment: Balance reserved by a previous `set_subs` call for one sub will be repatriated
		/// to the sender (*not* the original depositor).
		///
		/// The dispatch origin for this call must be _Signed_ and the sender must have a registered
		/// super-identity.
		///
		/// NOTE: This should not normally be used, but is provided in the case that the non-
		/// controller of an account is maliciously registered as a sub-account.
		#[weight = T::WeightInfo::quit_sub(T::MaxSubAccounts::get())]
		fn quit_sub(origin) {
			let sender = ensure_signed(origin)?;
			let (sup, _) = SuperOf::<T>::take(&sender).ok_or(Error::<T>::NotSub)?;
			SubsOf::<T>::mutate(&sup, |(ref mut subs_deposit, ref mut sub_ids)| {
				sub_ids.retain(|x| x != &sender);
				let deposit = T::SubAccountDeposit::get().min(*subs_deposit);
				*subs_deposit -= deposit;
				let _ = T::Currency::repatriate_reserved(&sup, &sender, deposit, BalanceStatus::Free);
				Self::deposit_event(RawEvent::SubIdentityRevoked(sender, sup.clone(), deposit));
			});
		}
	}
}

impl<T: Config> Module<T> {
	/// Get the subs of an account.
	pub fn subs(who: &T::AccountId) -> Vec<(T::AccountId, Data)> {
		SubsOf::<T>::get(who).1
			.into_iter()
			.filter_map(|a| SuperOf::<T>::get(&a).map(|x| (a, x.1)))
			.collect()
	}
}

