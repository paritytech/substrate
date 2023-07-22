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

//! ## Name Service: Register Friendly Account Aliases and Metadata
//!
//! # Index
//!
//! * [Key Terms](#key-terms)
//! * [Goals](#goals)
//! * [Limitations](#limitations)
//! * [Usage](#usage)
//!
//! The name service pallet provides a means to register names and subnames, also termed nodes,
//! via a commit reveal scheme. Names can act as aliases to addresses for a particular para ID, and
//! can be used by UIs to transfer tokens between accounts in a more user-friendly manner.
//!
//! ## Key Terms
//!
//! * commitment: A hash that represents a commitment to purchase a name registration. Any account
//!   can register a commitment by providing an owner address and a commitment hash - a
//!   blake2_256 hash of the desired name and a secret.
//! * node: Either a to-level name hash or a subnode record that exists in the service registry.
//! * name hash: A blake2_256 hash representation of a registered name.
//! * subnode: A child name of a registered name hash. Subnodes of a name can be registered
//!   recursively, so the depth a subnode can be registered is unbounded.
//! * registrar: Handles registration and deregistration of top-level names. It also allows the
//!   transfer of ownership of top-level names.
//! * resolver: Handles the mapping of a name registration to the metadata that can be assigned to
//!   it. An address (alongside the Para ID), text and unhashed name of the node.
//!
//! ## Goals
//!
//! The name service pallet is designed to allow account interactions to go through registered,
//! human-readable names. The targeted usage of the name service is to allow transferring of funds
//! to accounts using registered names as the recipient of the transfer, instead of their public
//! key.
//!
//! The pallet aims to be para-agnostic; any Para ID can be registered with the name service, and
//! provided alongside an address that is being set in the resolver. To register an address with a
//! corresponding para, that para ID must be registered with the name service.
//!
//! The name service in its current form aims to provide critical chain data to allow the usage of
//! human-readable names as address aliases, and assumes that UIs will handle the routing of
//! transfers using these names.
//!
//! ## Limitations
//!
//! The name service does not handle routing transfers between paras, and assumes the UI will handle
//! the resolution of public keys from name service nodes, and handle any teleporting required to
//! transfer funds using the name service.. A future version of the name service could explore such
//! functionality.
//!
//! ## Usage
//!
//! ### Registering a top-level name
//!
//! Using a commit [`Call::commit`] and reveal [`Call::reveal`] scheme, names can be registered on
//! the name service, and de-registered [`Call::deregister`] provided that no derived subnodes exist
//! in the registry.
//!
//! A commitment has up to `MaxCommitmentAge` blocks to be revealed before it expires. The
//! commitment can be removed by anyone after after the expiry block, or by the original depositor
//! before the expiry block, using [`Call::remove_commitment`].
//!
//! ### Registering a subnode
//!
//! Subnodes can be recursively registered [`Call::set_subnode_record`] on the system. Ownership can
//! be transferred between these subnodes, so they do not necessarily need to be tied with the owner
//! of parent nodes. Owners can degregister subnodes [`Call::deregister_subnode`], or anyone can if
//! the parent node has expired.
//!
//! ### Renewing
//!
//! //! * [`Call::renew`]
//!
//! Node ownership can be extended by providing a new expiry block. The fee corresponding to the new
//! expiry will be deducted from a provided fee-payer account.
//!
//! ### Transferring Ownership
//!
//! * [`Call::transfer`]
//!
//! Nodes can be transferred to a new owner. Transferring a node to a new owner will also transfer
//! the node deposit to the new owner.
//!
//! ### Using Resolvers
//!
//! An address, human-readable name and text can be registered under a node.
//!
//! ### Setting an Address
//!
//! * [`Call::set_address`]
//!
//! The address acts as the underlying account that the node is aliasing when used for transferring
//! tokens. Along with the address itself, a suffix is also provided, which aliases the registered
//! para id. The para id is stored in the resolver alongside the address.
//!
//! ### Setting a Name
//!
//! * [`Call::set_name`]
//!
//! Setting the name of a node is a permissionless call. The provided name must match what was
//! originally registered, e.g. hash(name) must equal name_hash. Doing so provides a human-readable
//! representation of the hash, and acts as a verification method for UIs for the name hash.
//!
//! ### Setting Text
//!
//! * [`Call::set_text`]
//!
//! The owner of a name hash can also set an ambiguous text record to give any miscellaneous text
//! data they want to store alongside the name.
//!
//! ### Domain Registration
//!
//! * [`Call::register_domain`]
//!
//! Domains must be registered with the name service before addresses can be set the assigned
//! `para_id` for them. Domain registration can only be done by the root origin, and intended to be
//! voted in by governance.
//!
//! ### Domain Deregistration
//!
//! * [`Call::deregister_domain`]
//!
//! Domains can also be deregistered by the root origin, and intended to be voted in by governance.

#![cfg_attr(not(feature = "std"), no_std)]
use frame_support::{ensure, pallet_prelude::*, traits::Get, DefaultNoBound};
use sp_std::vec::Vec;

pub use crate::types::*;
pub use pallet::*;
pub use weights::WeightInfo;

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
mod commit_reveal;
mod misc;
mod registrar;
mod resolver;
mod subnodes;
mod types;
pub mod weights;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::traits::{OnUnbalanced, ReservableCurrency, StorageVersion};
	use frame_system::{ensure_signed, pallet_prelude::*};
	use sp_runtime::traits::{Convert, Zero};
	use sp_std::vec::Vec;

	/// The current storage version.
	const STORAGE_VERSION: StorageVersion = StorageVersion::new(1);

	// The struct on which we build all of our Pallet logic.
	#[pallet::pallet]
	#[pallet::storage_version(STORAGE_VERSION)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: weights::WeightInfo;

		/// The Currency handler for this pallet.
		type Currency: ReservableCurrency<Self::AccountId>;

		/// Convert the block number into a balance.
		type BlockNumberToBalance: Convert<BlockNumberFor<Self>, BalanceOf<Self>>;

		/// The account where registration fees are paid to.
		type RegistrationFeeHandler: OnUnbalanced<NegativeImbalanceOf<Self>>;

		/// The amount of blocks a user needs to wait after a Commitment before revealing.
		#[pallet::constant]
		type MinCommitmentAge: Get<BlockNumberFor<Self>>;

		/// The amount of blocks after a commitment is created for before it expires.
		#[pallet::constant]
		type MaxCommitmentAge: Get<BlockNumberFor<Self>>;

		/// The bound on the length a name can be registered for. Applies to initial registration
		/// and renewing.
		#[pallet::constant]
		type MaxRegistrationLength: Get<BlockNumberFor<Self>>;

		/// Maximum length of a name.
		#[pallet::constant]
		type MaxNameLength: Get<u32>;

		/// Maximum length for metadata text.
		#[pallet::constant]
		type MaxTextLength: Get<u32>;

		// Maximum length for a para registration suffix.
		#[pallet::constant]
		type MaxSuffixLength: Get<u32>;

		/// An interface to access the name service resolver.
		type NameServiceResolver: NameServiceResolver<Self>;
	}

	/// Domain Registrations.
	///
	/// A Para ID needs to be provided alongside a suffix to represent the registered domain.
	#[pallet::storage]
	pub(super) type DomainRegistrations<T: Config> =
		CountedStorageMap<_, Twox64Concat, u32, BoundedSuffixOf<T>>;

	/// A reverse lookup from a suffix the para id owner.
	///
	/// This is used to resolve suffixes to para IDs.
	#[pallet::storage]
	pub type ReverseDomainsLookup<T: Config> =
		CountedStorageMap<_, Twox64Concat, BoundedSuffixOf<T>, u32, OptionQuery>;

	/// The deposit a user needs to make in order to commit to a name registration. A value of
	/// A value of `None` will disable commitments and therefore the registration of new names.
	#[pallet::storage]
	pub type CommitmentDeposit<T: Config> = StorageValue<_, BalanceOf<T>, OptionQuery>;

	/// The deposit a user needs to place to keep their subnodes in storage.
	/// A value of `None` will disable subnode registrations.
	#[pallet::storage]
	pub type SubNodeDeposit<T: Config> = StorageValue<_, BalanceOf<T>, OptionQuery>;

	/// Registration fee for registering a 3-letter name.
	#[pallet::storage]
	pub type TierThreeLetters<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

	/// Registration fee for registering a 4-letter name.
	#[pallet::storage]
	pub type TierFourLetters<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

	/// Default registration fee for 5+ letter names.
	#[pallet::storage]
	pub type TierDefault<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

	/// Registration fee per block.
	#[pallet::storage]
	pub type RegistrationFeePerBlock<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

	/// The deposit taken per byte of storage used.
	#[pallet::storage]
	pub type PerByteFee<T: Config> = StorageValue<_, BalanceOf<T>, ValueQuery>;

	/// Name Commitments
	#[pallet::storage]
	pub(super) type Commitments<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		CommitmentHash,
		Commitment<T::AccountId, BalanceOf<T>, BlockNumberFor<T>>,
	>;

	/// Name Registrations
	#[pallet::storage]
	pub(super) type Registrations<T: Config> = CountedStorageMap<
		_,
		Twox64Concat,
		NameHash,
		Registration<T::AccountId, BalanceOf<T>, BlockNumberFor<T>>,
	>;

	/// This resolver maps name hashes to a tuple of the account and `para_id` associated with the
	/// account.
	#[pallet::storage]
	pub(super) type AddressResolver<T: Config> =
		StorageMap<_, Blake2_128Concat, NameHash, (T::AccountId, u32)>;

	/// This resolver maps name hashes to the human-readable name of the hash.
	#[pallet::storage]
	pub(super) type NameResolver<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		NameHash,
		BytesStorage<T::AccountId, BalanceOf<T>, BoundedNameOf<T>>,
	>;

	/// This resolver maps name hashes to arbitrary human-readable text record.
	#[pallet::storage]
	pub(super) type TextResolver<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		NameHash,
		BytesStorage<T::AccountId, BalanceOf<T>, BoundedTextOf<T>>,
	>;

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		pub commitment_deposit: Option<BalanceOf<T>>,
		pub subnode_deposit: Option<BalanceOf<T>>,
		pub tier_three_letters: BalanceOf<T>,
		pub tier_four_letters: BalanceOf<T>,
		pub tier_default: BalanceOf<T>,
		pub registration_fee_per_block: BalanceOf<T>,
		pub per_byte_fee: BalanceOf<T>,
	}

	impl<T: Config> Default for GenesisConfig<T> {
		fn default() -> Self {
			Self {
				commitment_deposit: None,
				subnode_deposit: None,
				tier_three_letters: Zero::zero(),
				tier_four_letters: Zero::zero(),
				tier_default: Zero::zero(),
				registration_fee_per_block: <BalanceOf<T>>::from(1u32),
				per_byte_fee: <BalanceOf<T>>::from(1u32),
			}
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> BuildGenesisConfig for GenesisConfig<T> {
		fn build(&self) {
			if let Some(commitment_deposit) = self.commitment_deposit {
				CommitmentDeposit::<T>::put(commitment_deposit);
			}
			if let Some(subnode_deposit) = self.subnode_deposit {
				SubNodeDeposit::<T>::put(subnode_deposit);
			}
			TierThreeLetters::<T>::put(self.tier_three_letters);
			TierFourLetters::<T>::put(self.tier_four_letters);
			TierDefault::<T>::put(self.tier_default);
			RegistrationFeePerBlock::<T>::put(self.registration_fee_per_block);
			PerByteFee::<T>::put(self.per_byte_fee);
		}
	}

	// Your Pallet's events.
	#[pallet::event]
	#[pallet::generate_deposit(pub(crate) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A para has registered.
		DomainRegistered { para_id: u32, suffix: BoundedSuffixOf<T> },
		/// A para has deregistered.
		DomainDeregistered { para_id: u32 },
		/// A new `Commitment` has taken place.
		Committed { depositor: T::AccountId, owner: T::AccountId, hash: CommitmentHash },
		/// A new `Registration` has taken added.
		NameRegistered { name_hash: NameHash, owner: T::AccountId },
		/// A `Registration` has been transferred to a new owner.
		NewOwner { from: T::AccountId, to: T::AccountId },
		/// A `Registration` has been renewed.
		NameRenewed { name_hash: NameHash, expires: BlockNumberFor<T> },
		/// An address has been set for a name hash to resolve to.
		AddressSet { name_hash: NameHash, address: T::AccountId },
		/// An name has been set as a reverse lookup for a name hash. You can query storage to see
		/// what the name is.
		NameSet { name_hash: NameHash },
		/// An address has been set for a name hash to resolve to. You can query storage to see
		/// what text was set.
		TextSet { name_hash: NameHash },
		/// An address was deregistered.
		AddressDeregistered { name_hash: NameHash },
	}

	// Your Pallet's error messages.
	#[pallet::error]
	#[cfg_attr(test, derive(PartialEq))]
	pub enum Error<T> {
		/// It has not passed the minimum waiting period to reveal a commitment.
		TooEarlyToReveal,
		/// Commitment deposits have been disabled and commitments cannot be registered.
		CommitmentsDisabled,
		/// Subnode deposits have been disabled and subnodes cannot be registered.
		SubNodesDisabled,
		/// This suffix already exists in storage.
		SuffixExists,
		/// The provided domain ID already exists.
		DomainExists,
		/// This commitment hash already exists in storage.
		CommitmentExists,
		/// The commitment cannot yet be removed. Has not expired.
		CommitmentNotExpired,
		/// This commitment does not exist.
		CommitmentNotFound,
		/// A `Registration` of this name already exists.
		RegistrationExists,
		/// This registration has not yet expired.
		RegistrationNotExpired,
		/// This registration does not exist.
		RegistrationNotFound,
		/// The provided registration length is too long.
		MaxRegistrationLengthExceeded,
		/// Name is too short to be registered.
		NameTooShort,
		/// The name was longer than the configured limit.
		NameLengthExceeded,
		/// The text was longer than the configured limit.
		TextLengthExceeded,
		/// The account is not the name owner.
		NotOwner,
		/// Cannot renew this registration.
		RegistrationHasNoExpiry,
		/// Renew expiry time is not in the future.
		ExpiryInvalid,
		/// The name provided does not match the expected hash.
		BadName,
		/// The para ID was not found.
		DomainNotFound,
	}

	// Your Pallet's callable functions.
	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Force the registration of a name hash. It will overwrite any existing name registration,
		/// returning the deposit to the original owner.
		///
		/// Can only be called by the Root origin.
		#[pallet::call_index(0)]
		#[pallet::weight(T::WeightInfo::force_register())]
		pub fn force_register(
			origin: OriginFor<T>,
			name_hash: NameHash,
			who: T::AccountId,
			maybe_expiry: Option<BlockNumberFor<T>>,
		) -> DispatchResult {
			ensure_root(origin)?;
			Self::do_register(name_hash, who, maybe_expiry, None)?;
			Ok(())
		}

		/// Force the de-registration of a name hash. It will delete any existing name registration,
		/// returning the deposit to the original owner.
		///
		/// Can only be called by the Root origin.
		#[pallet::call_index(1)]
		#[pallet::weight(T::WeightInfo::force_deregister())]
		pub fn force_deregister(origin: OriginFor<T>, name_hash: NameHash) -> DispatchResult {
			ensure_root(origin)?;
			Self::do_deregister(name_hash);
			Ok(())
		}

		/// Allow a sender to commit to a new name registration on behalf of the `owner`. By making
		/// a commitment, the sender will reserve a deposit until the name is revealed or the
		/// commitment is removed.
		///
		/// The commitment hash should be the `bake2_256(name: <u8, MaxNameLength>, secret: u64)`,
		/// which allows the sender to keep name being registered secret until it is revealed.
		///
		/// The `name` must be at least 3 characters long.
		#[pallet::call_index(2)]
		#[pallet::weight(T::WeightInfo::commit())]
		pub fn commit(
			origin: OriginFor<T>,
			owner: T::AccountId,
			commitment_hash: CommitmentHash,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			Self::do_commit(sender, owner, commitment_hash)?;
			Ok(())
		}

		/// Allow a sender to reveal a previously committed name registration on behalf of the
		/// committed `owner`. By revealing the name, the sender will pay a non-refundable
		/// registration fee.
		#[pallet::call_index(3)]
		#[pallet::weight(T::WeightInfo::reveal(name.len() as u32))]
		pub fn reveal(
			origin: OriginFor<T>,
			name: Vec<u8>,
			secret: u64,
			length: BlockNumberFor<T>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let name_bounded: BoundedVec<u8, T::MaxNameLength> =
				BoundedVec::try_from(name).map_err(|_| Error::<T>::NameLengthExceeded)?;
			Self::do_reveal(sender, name_bounded.to_vec(), secret, length)?;
			Ok(())
		}

		/// Allows anyone to remove a commitment that has expired the reveal period.
		///
		/// By doing so, the commitment deposit is returned to the original depositor.
		#[pallet::call_index(4)]
		#[pallet::weight(T::WeightInfo::remove_commitment())]
		pub fn remove_commitment(
			origin: OriginFor<T>,
			commitment_hash: CommitmentHash,
		) -> DispatchResult {
			ensure_signed_or_root(origin)?;
			let commitment = Self::get_commitment(commitment_hash)?;
			let block_number = frame_system::Pallet::<T>::block_number();
			ensure!(
				Self::is_commitment_expired(&commitment, &block_number),
				Error::<T>::CommitmentNotExpired
			);
			Self::do_remove_commitment(&commitment_hash, &commitment);
			Ok(())
		}

		/// Transfers the ownership and deposits of a name registration to a new owner.
		///
		/// Can only be called by the existing owner of the name registration.
		#[pallet::call_index(5)]
		#[pallet::weight(T::WeightInfo::transfer())]
		pub fn transfer(
			origin: OriginFor<T>,
			new_owner: T::AccountId,
			name_hash: NameHash,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let registration = Self::get_registration(name_hash)?;
			ensure!(Self::is_owner(&registration, &sender), Error::<T>::NotOwner);
			Self::do_transfer_ownership(name_hash, new_owner)?;
			Ok(())
		}

		/// Allows any sender to extend the registration of an existing name.
		///
		/// By doing so, the sender will pay the non-refundable registration extension fee.
		#[pallet::call_index(6)]
		#[pallet::weight(T::WeightInfo::renew())]
		pub fn renew(
			origin: OriginFor<T>,
			name_hash: NameHash,
			expiry: BlockNumberFor<T>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			Self::do_renew(sender, name_hash, expiry)?;
			Ok(())
		}

		/// Deregister a registered name.
		///
		/// If the registration is still valid, only the owner of the name can make this call.
		///
		/// If the registration is expired, then anyone can call this function to make the name
		/// available.
		#[pallet::call_index(7)]
		#[pallet::weight(T::WeightInfo::deregister())]
		pub fn deregister(origin: OriginFor<T>, name_hash: NameHash) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let registration =
				Registrations::<T>::get(name_hash).ok_or(Error::<T>::RegistrationNotFound)?;
			// If the registration is expired, anyone can trigger deregister.
			if !Self::is_expired(&registration) {
				ensure!(Self::is_owner(&registration, &sender), Error::<T>::NotOwner);
			}
			Self::do_deregister(name_hash);
			Ok(())
		}

		/// Register a subnode (child) name record.
		///
		/// Validates the length of the provided label, returning an error if it surpasses the max
		/// supported name length.
		#[pallet::call_index(8)]
		#[pallet::weight(T::WeightInfo::set_subnode_record(label.len() as u32))]
		pub fn set_subnode_record(
			origin: OriginFor<T>,
			parent_hash: NameHash,
			label: Vec<u8>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let label_bounded: BoundedVec<u8, T::MaxNameLength> =
				BoundedVec::try_from(label).map_err(|_| Error::<T>::NameLengthExceeded)?;
			Self::do_set_subnode_record(sender, parent_hash, &label_bounded)?;
			Ok(())
		}

		/// Deregister a subnode (subdomain) record.
		///
		/// Validates the subnode registration existance, ownership and expiry before executing
		/// deregistration.
		///
		/// NOTES:
		/// * If subnode is expired, deregistering this subnode becomes permissionless.
		/// * Only the owner can deregister the node if the expiry block has not yet passed.
		#[pallet::call_index(9)]
		#[pallet::weight(T::WeightInfo::deregister_subnode())]
		pub fn deregister_subnode(
			origin: OriginFor<T>,
			parent_hash: NameHash,
			label_hash: NameHash,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let subnode_hash = Self::subnode_hash(parent_hash, label_hash);
			let subnode_registration = Self::get_registration(subnode_hash)?;
			// The owner isn't calling, We check that the parent registration exists, which means
			// this subnode is still valid.
			if !Self::is_owner(&subnode_registration, &sender) {
				ensure!(
					Self::get_registration(parent_hash).is_err(),
					Error::<T>::RegistrationNotExpired
				);
			}
			Self::do_deregister(subnode_hash);
			Ok(())
		}

		/// Sets an owner for a subnode record.
		///
		/// Only the current owner can re-assign ownership of the subnode.
		#[pallet::call_index(10)]
		#[pallet::weight(T::WeightInfo::set_subnode_owner())]
		pub fn set_subnode_owner(
			origin: OriginFor<T>,
			parent_hash: NameHash,
			label_hash: NameHash,
			new_owner: T::AccountId,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			Self::do_set_subnode_owner(sender, parent_hash, label_hash, new_owner)?;
			Ok(())
		}

		/// Sets an address of a registered node.
		///
		/// This call sets an address the name hash is aliasing, as well as the `para_id` associated
		/// with it, which is determined by the `suffix` parameter, with the latter dictating which
		/// para the address belongs to.
		#[pallet::call_index(11)]
		#[pallet::weight(T::WeightInfo::set_address())]
		pub fn set_address(
			origin: OriginFor<T>,
			name_hash: NameHash,
			address: T::AccountId, // TODO: should be agnostic address from any chain.
			suffix: BoundedSuffixOf<T>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			// resolve the para_id with the provided `suffix`.
			let para_id =
				ReverseDomainsLookup::<T>::get(&suffix).ok_or(Error::<T>::DomainNotFound)?;

			let registration =
				Registrations::<T>::get(name_hash).ok_or(Error::<T>::RegistrationNotFound)?;
			ensure!(Self::is_owner(&registration, &sender), Error::<T>::NotOwner);

			T::NameServiceResolver::set_address(name_hash, address, para_id, sender)?;
			Ok(())
		}

		/// Register the raw name for a given name hash. This can be used as a reverse lookup for
		/// front-ends.
		///
		/// This is a permissionless function that anyone can call who is willing to place a deposit
		/// to store this data on chain.
		#[pallet::call_index(12)]
		#[pallet::weight(T::WeightInfo::set_name(name.len() as u32))]
		pub fn set_name(
			origin: OriginFor<T>,
			name_hash: NameHash,
			name: Vec<u8>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let name_bounded: BoundedVec<u8, T::MaxNameLength> =
				BoundedVec::try_from(name).map_err(|_| Error::<T>::NameLengthExceeded)?;
			ensure!(Registrations::<T>::contains_key(name_hash), Error::<T>::RegistrationNotFound);
			T::NameServiceResolver::set_name(name_hash, name_bounded, sender)?;
			Ok(())
		}

		/// Set text record for a node.
		///
		/// Allows arbitrary text to be associated with the node.
		///
		/// Simply adds additional metadata to the node. No routing or aliasing is done with this
		/// value.
		#[pallet::call_index(13)]
		#[pallet::weight(T::WeightInfo::set_text(text.len() as u32))]
		pub fn set_text(
			origin: OriginFor<T>,
			name_hash: NameHash,
			text: Vec<u8>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let text_bounded: BoundedVec<u8, T::MaxTextLength> =
				BoundedVec::try_from(text).map_err(|_| Error::<T>::TextLengthExceeded)?;

			let registration =
				Registrations::<T>::get(name_hash).ok_or(Error::<T>::RegistrationNotFound)?;
			ensure!(Self::is_owner(&registration, &sender), Error::<T>::NotOwner);
			T::NameServiceResolver::set_text(name_hash, text_bounded, sender)?;
			Ok(())
		}

		/// Inserts a suffix for a para ID.
		///
		/// Overwrites existing values if already present.
		/// Can only be called by the Root origin.
		#[pallet::call_index(14)]
		#[pallet::weight(T::WeightInfo::register_domain())]
		pub fn register_domain(origin: OriginFor<T>, para: Domain<T>) -> DispatchResult {
			ensure_root(origin)?;
			ensure!(
				!ReverseDomainsLookup::<T>::contains_key(&para.suffix),
				Error::<T>::SuffixExists
			);
			ensure!(!DomainRegistrations::<T>::contains_key(para.id), Error::<T>::DomainExists,);
			DomainRegistrations::<T>::insert(para.id, para.suffix.clone());
			ReverseDomainsLookup::<T>::insert(para.suffix.clone(), para.id);
			Self::deposit_event(Event::<T>::DomainRegistered {
				para_id: para.id,
				suffix: para.suffix,
			});
			Ok(())
		}

		/// Can only be called by the Root origin.
		#[pallet::call_index(15)]
		#[pallet::weight(T::WeightInfo::deregister_domain())]
		pub fn deregister_domain(origin: OriginFor<T>, para_id: u32) -> DispatchResult {
			ensure_root(origin)?;
			let suffix =
				DomainRegistrations::<T>::get(para_id).ok_or(Error::<T>::DomainNotFound)?;

			DomainRegistrations::<T>::remove(&para_id);
			ReverseDomainsLookup::<T>::remove(&suffix);
			Self::deposit_event(Event::<T>::DomainDeregistered { para_id });
			Ok(())
		}

		/// Update configurations for the name service. The origin for this call must be
		/// Root.
		///
		/// # Arguments
		///
		/// * `commitment_deposit` - Set [`CommitmentDeposit`].
		/// * `subnode_deposit` - Set [`SubNodeDeposit`].
		/// * `tier_three_letters` - Set [`TierThreeLetters`].
		/// * `tier_four_letters` - Set [`TierFourLetters`].
		/// * `tier_default` - Set [`TierDefault`].
		/// * `registration_fee_per_block` - Set [`RegistrationFeePerBlock`].
		/// * `per_byte_fee` - Set [`PerByteFee`].
		#[pallet::call_index(16)]
		#[pallet::weight(T::WeightInfo::set_configs())]
		pub fn set_configs(
			origin: OriginFor<T>,
			commitment_deposit: ConfigOp<BalanceOf<T>>,
			subnode_deposit: ConfigOp<BalanceOf<T>>,
			tier_three_letters: ConfigOp<BalanceOf<T>>,
			tier_four_letters: ConfigOp<BalanceOf<T>>,
			tier_default: ConfigOp<BalanceOf<T>>,
			registration_fee_per_block: ConfigOp<BalanceOf<T>>,
			per_byte_fee: ConfigOp<BalanceOf<T>>,
		) -> DispatchResult {
			ensure_root(origin)?;

			macro_rules! config_op_exp {
				($storage:ty, $op:ident) => {
					match $op {
						ConfigOp::Noop => (),
						ConfigOp::Set(v) => <$storage>::put(v),
						ConfigOp::Remove => <$storage>::kill(),
					}
				};
			}

			config_op_exp!(CommitmentDeposit::<T>, commitment_deposit);
			config_op_exp!(SubNodeDeposit::<T>, subnode_deposit);
			config_op_exp!(TierThreeLetters::<T>, tier_three_letters);
			config_op_exp!(TierFourLetters::<T>, tier_four_letters);
			config_op_exp!(TierDefault::<T>, tier_default);
			config_op_exp!(RegistrationFeePerBlock::<T>, registration_fee_per_block);
			config_op_exp!(PerByteFee::<T>, per_byte_fee);

			Ok(())
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn integrity_test() {
			assert!(T::MaxNameLength::get() > 0, "Max name length cannot be zero");
			assert!(T::MaxTextLength::get() > 0, "Max text length cannot be zero");
			assert!(T::MaxSuffixLength::get() > 0, "Max suffix length cannot be zero");
		}
	}
}
