// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

//! A simple name service that can be used to give accounts friendly names.

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;
use sp_runtime::traits::{Saturating};
use frame_support::{decl_module, decl_error, decl_event, decl_storage, ensure, RuntimeDebug};
use frame_support::dispatch::DispatchResult;
use frame_support::traits::{
	Currency, ReservableCurrency, Get, EnsureOrigin, OnUnbalanced,
	WithdrawReason, ExistenceRequirement::KeepAlive, Imbalance,
};
use frame_system::ensure_signed;
use codec::{Encode, Decode};

mod mock;
mod tests;
mod benchmarking;

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;
type NegativeImbalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::NegativeImbalance;

pub trait WeightInfo {}

/// The module's config trait.
pub trait Trait: frame_system::Trait {

	/// The currency trait.
	type Currency: ReservableCurrency<Self::AccountId>;

	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;

	/// Origin that can have high level control over the name-service pallet.
	type ManagerOrigin: EnsureOrigin<Self::Origin>;

	/// Origin that can set permanent ownership of a name to an account.
	type PermanenceOrigin: EnsureOrigin<Self::Origin>;

	/// Time available between subsequent bids for a name.
	type BiddingPeriod: Get<Self::BlockNumber>;

	/// Time available after bidding has completed for the winner to claim their name.
	type ClaimPeriod: Get<Self::BlockNumber>;

	/// One ownership period, which can be multiplied through exponential deposit.
	type OwnershipPeriod: Get<Self::BlockNumber>;

	/// Handler for the unbalanced decrease when funds are burned.
	type BurnDestination: OnUnbalanced<NegativeImbalanceOf<Self>>;

	/// Minimum length for a publicly available name.
	type MinLength: Get<usize>;

	/// Maximum length for a publicly available name.
	type MaxLength: Get<usize>;

	/// Minimum Bid for a name.
	type MinBid: Get<BalanceOf<Self>>;

	/// Weight information for extrinsics in this pallet.
	type WeightInfo: WeightInfo;
}

#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug)]
pub enum Name<AccountId, BlockNumber, Balance> {
	Available,
	Bidding {
		who: AccountId,
		expiration: BlockNumber,
		amount: Balance,
	},
	Owned {
		who: AccountId,
		expiration: Option<BlockNumber>,
	}
}

impl<AccountId, BlockNumber, Balance> Default for Name<AccountId, BlockNumber, Balance> {
	fn default() -> Self {
		Name::Available
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as NameService {
		/// The lookup from name to account.
		pub Accounts: map hasher(blake2_128_concat) Vec<u8> => Name<T::AccountId, T::BlockNumber, BalanceOf<T>>;
	}
}

decl_event!(
	pub enum Event<T> where
		Balance = BalanceOf<T>,
		<T as frame_system::Trait>::AccountId,
		<T as frame_system::Trait>::BlockNumber,
	{
		BidPlaced(AccountId, Vec<u8>, Balance, BlockNumber),
		NameClaimed(AccountId, Vec<u8>, BlockNumber),
		NameFreed(Vec<u8>),
		NameSet(Vec<u8>),
	}
);

decl_error! {
	pub enum Error for Module<T: Trait> {
		/// The current state of the name does not match this step in the state machine.
		UnexpectedState,
		/// The name provided does not follow the configured rules.
		InvalidName,
		/// The bid is invalid.
		InvalidBid,
		/// The claim is invalid.
		InvalidClaim,
		/// User is not the current bidder.
		NotBidder,
		/// The name has not expired in bidding or ownership.
		NotExpired,
		/// The name is already available.
		AlreadyAvailable,
		/// The name is permanent.
		Permanent,
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin, system = frame_system {
		//TODO: Expose Constants

		fn deposit_event() = default;

		#[weight = 0]
		fn set_name(origin, name: Vec<u8>, state: Name<T::AccountId, T::BlockNumber, BalanceOf<T>>) {
			T::ManagerOrigin::ensure_origin(origin)?;
			// TODO: Make safer with regards to setting or removing `Bidding` state.
			Accounts::<T>::insert(&name, state);
			Self::deposit_event(RawEvent::NameSet(name));
		}

		#[weight = 0]
		fn make_permanent(origin, name: Vec<u8>) {
			T::PermanenceOrigin::ensure_origin(origin)?;
			Accounts::<T>::try_mutate(&name, |state| -> DispatchResult {
				match state {
					Name::Owned { expiration, .. } => {
						*expiration = None;
						Ok(())
					},
					_ => Err(Error::<T>::UnexpectedState)?
				}
			})?;
		}

		#[weight = 0]
		fn bid(origin, name: Vec<u8>, new_bid: BalanceOf<T>) {
			let new_bidder = ensure_signed(origin)?;
			Self::ensure_name_rules(&name, new_bid)?;

			let block_number = frame_system::Module::<T>::block_number();
			let new_expiration = block_number.saturating_add(T::BiddingPeriod::get());

			Accounts::<T>::try_mutate(&name, |state| -> DispatchResult {
				match state {
					// Name is available, we can directly transition this to Bidding.
					Name::Available => {
						T::Currency::reserve(&new_bidder, new_bid)?;
						*state = Name::Bidding {
							who: new_bidder.clone(),
							expiration: new_expiration,
							amount: new_bid
						};
						Ok(())
					},
					// Bid is ongoing, we need to check if the new bid is valid.
					Name::Bidding { who: current_bidder, expiration: current_expiration, amount: current_bid } => {
						// New bid must be before expiration and more than the current bid.
						if block_number < *current_expiration && *current_bid < new_bid {
							// Try to reserve the new amount and unreserve the old amount, handling the same bidder.
							if new_bidder == *current_bidder {
								// We check that new bid is greater than current bid, so this is safe.
								let bid_diff = new_bid - *current_bid;
								T::Currency::reserve(&new_bidder, bid_diff)?;
							} else {
								T::Currency::reserve(&new_bidder, new_bid)?;
								T::Currency::unreserve(&current_bidder, *current_bid);
							}
							*state = Name::Bidding {
								who: new_bidder.clone(),
								expiration: new_expiration,
								amount: new_bid
							};
							Ok(())
						} else {
							Err(Error::<T>::InvalidBid)?
						}
					},
					// Name is already owned, this is an invalid bid.
					Name::Owned { .. } => {
						Err(Error::<T>::InvalidBid)?
					}
				}
			})?;
			Self::deposit_event(RawEvent::BidPlaced(new_bidder, name, new_bid, new_expiration));
		}

		#[weight = 0]
		fn claim(origin, name: Vec<u8>, num_of_periods: u32) {
			let caller = ensure_signed(origin)?;
			ensure!(num_of_periods > 0, Error::<T>::InvalidClaim);

			let block_number = frame_system::Module::<T>::block_number();

			Accounts::<T>::try_mutate(&name, |state| -> DispatchResult {
				match state {
					Name::Available | Name::Owned { .. } => Err(Error::<T>::InvalidClaim)?,
					Name::Bidding { who: current_bidder, expiration, amount } => {
						ensure!(caller == *current_bidder, Error::<T>::NotBidder);
						ensure!(*expiration < block_number, Error::<T>::NotExpired);
						// If user only wants 1 period, just slash the reserve we already have.
						let mut credit = if num_of_periods == 1 {
							NegativeImbalanceOf::<T>::zero()
						} else {
							// User pays N^2 the price of the bid to own the name for N periods.
							let multiplier = num_of_periods.saturating_mul(num_of_periods);
							// We already have already reserved 1x deposit, so we just need to check
							// they can pay the rest...
							let withdraw_amount = amount.saturating_mul((multiplier - 1).into());
							T::Currency::withdraw(
								current_bidder,
								withdraw_amount,
								WithdrawReason::Fee.into(),
								KeepAlive
							)?
						};
						// Remove the rest from reserve
						credit.subsume(T::Currency::slash_reserved(current_bidder, *amount).0);
						T::BurnDestination::on_unbalanced(credit);
						// Grant ownership
						let ownership_expiration = T::OwnershipPeriod::get().saturating_mul(num_of_periods.into());
						*state = Name::Owned {
							who: current_bidder.clone(),
							expiration: Some(ownership_expiration),
						};
						Self::deposit_event(RawEvent::NameClaimed(caller, name.clone(), ownership_expiration));
						Ok(())
					},
				}
			})?;
		}

		#[weight = 0]
		fn free(origin, name: Vec<u8>) {
			let caller = ensure_signed(origin)?;
			let block_number = frame_system::Module::<T>::block_number();

			Accounts::<T>::try_mutate(&name, |state| -> DispatchResult {
				match state {
					// Name is already free, do nothing.
					Name::Available => Err(Error::<T>::AlreadyAvailable)?,
					// Name is in bidding period, check that it is past the bid expiration + claim period.
					Name::Bidding { who: current_bidder, expiration, amount } => {
						let free_block = expiration
							.saturating_add(T::BiddingPeriod::get())
							.saturating_add(T::ClaimPeriod::get());
						ensure!(free_block < block_number, Error::<T>::NotExpired);
						// Remove the bid, slashing the reserve.
						let credit = T::Currency::slash_reserved(current_bidder, *amount).0;
						T::BurnDestination::on_unbalanced(credit);
						*state = Name::Available;
						Ok(())
					},
					// Name is owned, check that it is past the ownership expiration or the current owner
					// is calling this function.
					Name::Owned { who: current_owner, expiration: maybe_expiration } => {
						if let Some(expiration) = maybe_expiration {
							if caller != *current_owner {
								ensure!(*expiration < block_number, Error::<T>::NotExpired);
							}
							*state = Name::Available;
							Ok(())
						} else {
							Err(Error::<T>::Permanent)?
						}
					},
				}
			})?;

			Self::deposit_event(RawEvent::NameFreed(name));
		}
	}
}

impl<T: Trait> Module<T> {
	// PUBLIC IMMUTABLES

	fn ensure_name_rules(name: &[u8], amount: BalanceOf<T>) -> DispatchResult {
		ensure!(name.len() >= T::MinLength::get(), Error::<T>::InvalidName);
		ensure!(name.len() <= T::MaxLength::get(), Error::<T>::InvalidName);
		ensure!(amount > T::MinBid::get(), Error::<T>::InvalidBid);
		Ok(())
	}

	// /// Lookup a name to get an AccountId, if there's one there.
	// pub fn lookup_name(name: Vec<u8>) -> Option<T::AccountId> {
	// 	Accounts::<T>::get(name).map(|x| match x {
	// 		Name::Owned { who, .. } => Some(who),
	// 		_ => None,
	// 	})
	// }

	// /// Lookup an address to get an Id, if there's one there.
	// pub fn lookup_address(
	// 	a: address::Address<T::AccountId, T::AccountIndex>
	// ) -> Option<T::AccountId> {
	// 	match a {
	// 		address::Address::Id(i) => Some(i),
	// 		address::Address::Index(i) => Self::lookup_index(i),
	// 	}
	// }
}

// impl<T: Trait> StaticLookup for Module<T> {
// 	type Source = address::Address<T::AccountId, Vec<u8>>;
// 	type Target = T::AccountId;

// 	fn lookup(a: Self::Source) -> Result<Self::Target, LookupError> {
// 		Self::lookup_name(a).ok_or(LookupError)
// 	}

// 	fn unlookup(a: Self::Target) -> Self::Source {
// 		Default::default();
// 		//address::Address::Id(a)
// 	}
// }
