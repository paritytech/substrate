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

//! # Proxy Pallet
//! A pallet allowing accounts to give permission to other accounts to dispatch types of calls from
//! their signed origin.
//!
//! The accounts to which permission is delegated may be required to announce the action that they
//! wish to execute some duration prior to execution happens. In this case, the target account may
//! reject the announcement and in doing so, veto the execution.
//!
//! - [`Config`]
//! - [`Call`]

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

mod benchmarking;
mod tests;
pub mod weights;

use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{
	dispatch::GetDispatchInfo,
	ensure,
	traits::{Currency, Get, InstanceFilter, IsSubType, IsType, OriginTrait, ReservableCurrency},
};
use frame_system::{self as system, ensure_signed, pallet_prelude::BlockNumberFor};
pub use pallet::*;
use scale_info::TypeInfo;
use sp_io::hashing::blake2_256;
use sp_runtime::{
	traits::{Dispatchable, Hash, Saturating, StaticLookup, TrailingZeroInput, Zero},
	DispatchError, DispatchResult, RuntimeDebug,
};
use sp_std::prelude::*;
pub use weights::WeightInfo;

type CallHashOf<T> = <<T as Config>::CallHasher as Hash>::Output;

type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

type AccountIdLookupOf<T> = <<T as frame_system::Config>::Lookup as StaticLookup>::Source;

/// The parameters under which a particular account has a proxy relationship with some other
/// account.
#[derive(
	Encode,
	Decode,
	Clone,
	Copy,
	Eq,
	PartialEq,
	Ord,
	PartialOrd,
	RuntimeDebug,
	MaxEncodedLen,
	TypeInfo,
)]
pub struct ProxyDefinition<AccountId, ProxyType, BlockNumber> {
	/// The account which may act on behalf of another.
	pub delegate: AccountId,
	/// A value defining the subset of calls that it is allowed to make.
	pub proxy_type: ProxyType,
	/// The number of blocks that an announcement must be in place for before the corresponding
	/// call may be dispatched. If zero, then no announcement is needed.
	pub delay: BlockNumber,
}

/// Details surrounding a specific instance of an announcement to make a call.
#[derive(Encode, Decode, Clone, Copy, Eq, PartialEq, RuntimeDebug, MaxEncodedLen, TypeInfo)]
pub struct Announcement<AccountId, Hash, BlockNumber> {
	/// The account which made the announcement.
	real: AccountId,
	/// The hash of the call to be made.
	call_hash: Hash,
	/// The height at which the announcement was made.
	height: BlockNumber,
}

#[frame_support::pallet]
pub mod pallet {
	use super::{DispatchResult, *};
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	/// Configuration trait.
	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// The overarching call type.
		type RuntimeCall: Parameter
			+ Dispatchable<RuntimeOrigin = Self::RuntimeOrigin>
			+ GetDispatchInfo
			+ From<frame_system::Call<Self>>
			+ IsSubType<Call<Self>>
			+ IsType<<Self as frame_system::Config>::RuntimeCall>;

		/// The currency mechanism.
		type Currency: ReservableCurrency<Self::AccountId>;

		/// A kind of proxy; specified with the proxy and passed in to the `IsProxyable` fitler.
		/// The instance filter determines whether a given call may be proxied under this type.
		///
		/// IMPORTANT: `Default` must be provided and MUST BE the the *most permissive* value.
		type ProxyType: Parameter
			+ Member
			+ Ord
			+ PartialOrd
			+ InstanceFilter<<Self as Config>::RuntimeCall>
			+ Default
			+ MaxEncodedLen;

		/// The base amount of currency needed to reserve for creating a proxy.
		///
		/// This is held for an additional storage item whose value size is
		/// `sizeof(Balance)` bytes and whose key size is `sizeof(AccountId)` bytes.
		#[pallet::constant]
		type ProxyDepositBase: Get<BalanceOf<Self>>;

		/// The amount of currency needed per proxy added.
		///
		/// This is held for adding 32 bytes plus an instance of `ProxyType` more into a
		/// pre-existing storage value. Thus, when configuring `ProxyDepositFactor` one should take
		/// into account `32 + proxy_type.encode().len()` bytes of data.
		#[pallet::constant]
		type ProxyDepositFactor: Get<BalanceOf<Self>>;

		/// The maximum amount of proxies allowed for a single account.
		#[pallet::constant]
		type MaxProxies: Get<u32>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;

		/// The maximum amount of time-delayed announcements that are allowed to be pending.
		#[pallet::constant]
		type MaxPending: Get<u32>;

		/// The type of hash used for hashing the call.
		type CallHasher: Hash;

		/// The base amount of currency needed to reserve for creating an announcement.
		///
		/// This is held when a new storage item holding a `Balance` is created (typically 16
		/// bytes).
		#[pallet::constant]
		type AnnouncementDepositBase: Get<BalanceOf<Self>>;

		/// The amount of currency needed per announcement made.
		///
		/// This is held for adding an `AccountId`, `Hash` and `BlockNumber` (typically 68 bytes)
		/// into a pre-existing storage value.
		#[pallet::constant]
		type AnnouncementDepositFactor: Get<BalanceOf<Self>>;
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Dispatch the given `call` from an account that the sender is authorised for through
		/// `add_proxy`.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// Parameters:
		/// - `real`: The account that the proxy will make a call on behalf of.
		/// - `force_proxy_type`: Specify the exact proxy type to be used and checked for this call.
		/// - `call`: The call to be made by the `real` account.
		#[pallet::call_index(0)]
		#[pallet::weight({
			let di = call.get_dispatch_info();
			(T::WeightInfo::proxy(T::MaxProxies::get())
				 // AccountData for inner call origin accountdata.
				.saturating_add(T::DbWeight::get().reads_writes(1, 1))
				.saturating_add(di.weight),
			di.class)
		})]
		pub fn proxy(
			origin: OriginFor<T>,
			real: AccountIdLookupOf<T>,
			force_proxy_type: Option<T::ProxyType>,
			call: Box<<T as Config>::RuntimeCall>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let real = T::Lookup::lookup(real)?;
			let def = Self::find_proxy(&real, &who, force_proxy_type)?;
			ensure!(def.delay.is_zero(), Error::<T>::Unannounced);

			Self::do_proxy(def, real, *call);

			Ok(())
		}

		/// Register a proxy account for the sender that is able to make calls on its behalf.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// Parameters:
		/// - `proxy`: The account that the `caller` would like to make a proxy.
		/// - `proxy_type`: The permissions allowed for this proxy account.
		/// - `delay`: The announcement period required of the initial proxy. Will generally be
		/// zero.
		#[pallet::call_index(1)]
		#[pallet::weight(T::WeightInfo::add_proxy(T::MaxProxies::get()))]
		pub fn add_proxy(
			origin: OriginFor<T>,
			delegate: AccountIdLookupOf<T>,
			proxy_type: T::ProxyType,
			delay: BlockNumberFor<T>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let delegate = T::Lookup::lookup(delegate)?;
			Self::add_proxy_delegate(&who, delegate, proxy_type, delay)
		}

		/// Unregister a proxy account for the sender.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// Parameters:
		/// - `proxy`: The account that the `caller` would like to remove as a proxy.
		/// - `proxy_type`: The permissions currently enabled for the removed proxy account.
		#[pallet::call_index(2)]
		#[pallet::weight(T::WeightInfo::remove_proxy(T::MaxProxies::get()))]
		pub fn remove_proxy(
			origin: OriginFor<T>,
			delegate: AccountIdLookupOf<T>,
			proxy_type: T::ProxyType,
			delay: BlockNumberFor<T>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let delegate = T::Lookup::lookup(delegate)?;
			Self::remove_proxy_delegate(&who, delegate, proxy_type, delay)
		}

		/// Unregister all proxy accounts for the sender.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// WARNING: This may be called on accounts created by `pure`, however if done, then
		/// the unreserved fees will be inaccessible. **All access to this account will be lost.**
		#[pallet::call_index(3)]
		#[pallet::weight(T::WeightInfo::remove_proxies(T::MaxProxies::get()))]
		pub fn remove_proxies(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::remove_all_proxy_delegates(&who);
			Ok(())
		}

		/// Spawn a fresh new account that is guaranteed to be otherwise inaccessible, and
		/// initialize it with a proxy of `proxy_type` for `origin` sender.
		///
		/// Requires a `Signed` origin.
		///
		/// - `proxy_type`: The type of the proxy that the sender will be registered as over the
		/// new account. This will almost always be the most permissive `ProxyType` possible to
		/// allow for maximum flexibility.
		/// - `index`: A disambiguation index, in case this is called multiple times in the same
		/// transaction (e.g. with `utility::batch`). Unless you're using `batch` you probably just
		/// want to use `0`.
		/// - `delay`: The announcement period required of the initial proxy. Will generally be
		/// zero.
		///
		/// Fails with `Duplicate` if this has already been called in this transaction, from the
		/// same sender, with the same parameters.
		///
		/// Fails if there are insufficient funds to pay for deposit.
		#[pallet::call_index(4)]
		#[pallet::weight(T::WeightInfo::create_pure(T::MaxProxies::get()))]
		pub fn create_pure(
			origin: OriginFor<T>,
			proxy_type: T::ProxyType,
			delay: BlockNumberFor<T>,
			index: u16,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			let pure = Self::pure_account(&who, &proxy_type, index, None);
			ensure!(!Proxies::<T>::contains_key(&pure), Error::<T>::Duplicate);

			let proxy_def =
				ProxyDefinition { delegate: who.clone(), proxy_type: proxy_type.clone(), delay };
			let bounded_proxies: BoundedVec<_, T::MaxProxies> =
				vec![proxy_def].try_into().map_err(|_| Error::<T>::TooMany)?;

			let deposit = T::ProxyDepositBase::get() + T::ProxyDepositFactor::get();
			T::Currency::reserve(&who, deposit)?;

			Proxies::<T>::insert(&pure, (bounded_proxies, deposit));
			Self::deposit_event(Event::PureCreated {
				pure,
				who,
				proxy_type,
				disambiguation_index: index,
			});

			Ok(())
		}

		/// Removes a previously spawned pure proxy.
		///
		/// WARNING: **All access to this account will be lost.** Any funds held in it will be
		/// inaccessible.
		///
		/// Requires a `Signed` origin, and the sender account must have been created by a call to
		/// `pure` with corresponding parameters.
		///
		/// - `spawner`: The account that originally called `pure` to create this account.
		/// - `index`: The disambiguation index originally passed to `pure`. Probably `0`.
		/// - `proxy_type`: The proxy type originally passed to `pure`.
		/// - `height`: The height of the chain when the call to `pure` was processed.
		/// - `ext_index`: The extrinsic index in which the call to `pure` was processed.
		///
		/// Fails with `NoPermission` in case the caller is not a previously created pure
		/// account whose `pure` call has corresponding parameters.
		#[pallet::call_index(5)]
		#[pallet::weight(T::WeightInfo::kill_pure(T::MaxProxies::get()))]
		pub fn kill_pure(
			origin: OriginFor<T>,
			spawner: AccountIdLookupOf<T>,
			proxy_type: T::ProxyType,
			index: u16,
			#[pallet::compact] height: BlockNumberFor<T>,
			#[pallet::compact] ext_index: u32,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let spawner = T::Lookup::lookup(spawner)?;

			let when = (height, ext_index);
			let proxy = Self::pure_account(&spawner, &proxy_type, index, Some(when));
			ensure!(proxy == who, Error::<T>::NoPermission);

			let (_, deposit) = Proxies::<T>::take(&who);
			T::Currency::unreserve(&spawner, deposit);

			Ok(())
		}

		/// Publish the hash of a proxy-call that will be made in the future.
		///
		/// This must be called some number of blocks before the corresponding `proxy` is attempted
		/// if the delay associated with the proxy relationship is greater than zero.
		///
		/// No more than `MaxPending` announcements may be made at any one time.
		///
		/// This will take a deposit of `AnnouncementDepositFactor` as well as
		/// `AnnouncementDepositBase` if there are no other pending announcements.
		///
		/// The dispatch origin for this call must be _Signed_ and a proxy of `real`.
		///
		/// Parameters:
		/// - `real`: The account that the proxy will make a call on behalf of.
		/// - `call_hash`: The hash of the call to be made by the `real` account.
		#[pallet::call_index(6)]
		#[pallet::weight(T::WeightInfo::announce(T::MaxPending::get(), T::MaxProxies::get()))]
		pub fn announce(
			origin: OriginFor<T>,
			real: AccountIdLookupOf<T>,
			call_hash: CallHashOf<T>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let real = T::Lookup::lookup(real)?;
			Proxies::<T>::get(&real)
				.0
				.into_iter()
				.find(|x| x.delegate == who)
				.ok_or(Error::<T>::NotProxy)?;

			let announcement = Announcement {
				real: real.clone(),
				call_hash,
				height: system::Pallet::<T>::block_number(),
			};

			Announcements::<T>::try_mutate(&who, |(ref mut pending, ref mut deposit)| {
				pending.try_push(announcement).map_err(|_| Error::<T>::TooMany)?;
				Self::rejig_deposit(
					&who,
					*deposit,
					T::AnnouncementDepositBase::get(),
					T::AnnouncementDepositFactor::get(),
					pending.len(),
				)
				.map(|d| {
					d.expect("Just pushed; pending.len() > 0; rejig_deposit returns Some; qed")
				})
				.map(|d| *deposit = d)
			})?;
			Self::deposit_event(Event::Announced { real, proxy: who, call_hash });

			Ok(())
		}

		/// Remove a given announcement.
		///
		/// May be called by a proxy account to remove a call they previously announced and return
		/// the deposit.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// Parameters:
		/// - `real`: The account that the proxy will make a call on behalf of.
		/// - `call_hash`: The hash of the call to be made by the `real` account.
		#[pallet::call_index(7)]
		#[pallet::weight(T::WeightInfo::remove_announcement(
			T::MaxPending::get(),
			T::MaxProxies::get()
		))]
		pub fn remove_announcement(
			origin: OriginFor<T>,
			real: AccountIdLookupOf<T>,
			call_hash: CallHashOf<T>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let real = T::Lookup::lookup(real)?;
			Self::edit_announcements(&who, |ann| ann.real != real || ann.call_hash != call_hash)?;

			Ok(())
		}

		/// Remove the given announcement of a delegate.
		///
		/// May be called by a target (proxied) account to remove a call that one of their delegates
		/// (`delegate`) has announced they want to execute. The deposit is returned.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// Parameters:
		/// - `delegate`: The account that previously announced the call.
		/// - `call_hash`: The hash of the call to be made.
		#[pallet::call_index(8)]
		#[pallet::weight(T::WeightInfo::reject_announcement(
			T::MaxPending::get(),
			T::MaxProxies::get()
		))]
		pub fn reject_announcement(
			origin: OriginFor<T>,
			delegate: AccountIdLookupOf<T>,
			call_hash: CallHashOf<T>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let delegate = T::Lookup::lookup(delegate)?;
			Self::edit_announcements(&delegate, |ann| {
				ann.real != who || ann.call_hash != call_hash
			})?;

			Ok(())
		}

		/// Dispatch the given `call` from an account that the sender is authorized for through
		/// `add_proxy`.
		///
		/// Removes any corresponding announcement(s).
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// Parameters:
		/// - `real`: The account that the proxy will make a call on behalf of.
		/// - `force_proxy_type`: Specify the exact proxy type to be used and checked for this call.
		/// - `call`: The call to be made by the `real` account.
		#[pallet::call_index(9)]
		#[pallet::weight({
			let di = call.get_dispatch_info();
			(T::WeightInfo::proxy_announced(T::MaxPending::get(), T::MaxProxies::get())
				 // AccountData for inner call origin accountdata.
				.saturating_add(T::DbWeight::get().reads_writes(1, 1))
				.saturating_add(di.weight),
			di.class)
		})]
		pub fn proxy_announced(
			origin: OriginFor<T>,
			delegate: AccountIdLookupOf<T>,
			real: AccountIdLookupOf<T>,
			force_proxy_type: Option<T::ProxyType>,
			call: Box<<T as Config>::RuntimeCall>,
		) -> DispatchResult {
			ensure_signed(origin)?;
			let delegate = T::Lookup::lookup(delegate)?;
			let real = T::Lookup::lookup(real)?;
			let def = Self::find_proxy(&real, &delegate, force_proxy_type)?;

			let call_hash = T::CallHasher::hash_of(&call);
			let now = system::Pallet::<T>::block_number();
			Self::edit_announcements(&delegate, |ann| {
				ann.real != real ||
					ann.call_hash != call_hash ||
					now.saturating_sub(ann.height) < def.delay
			})
			.map_err(|_| Error::<T>::Unannounced)?;

			Self::do_proxy(def, real, *call);

			Ok(())
		}
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A proxy was executed correctly, with the given.
		ProxyExecuted { result: DispatchResult },
		/// A pure account has been created by new proxy with given
		/// disambiguation index and proxy type.
		PureCreated {
			pure: T::AccountId,
			who: T::AccountId,
			proxy_type: T::ProxyType,
			disambiguation_index: u16,
		},
		/// An announcement was placed to make a call in the future.
		Announced { real: T::AccountId, proxy: T::AccountId, call_hash: CallHashOf<T> },
		/// A proxy was added.
		ProxyAdded {
			delegator: T::AccountId,
			delegatee: T::AccountId,
			proxy_type: T::ProxyType,
			delay: BlockNumberFor<T>,
		},
		/// A proxy was removed.
		ProxyRemoved {
			delegator: T::AccountId,
			delegatee: T::AccountId,
			proxy_type: T::ProxyType,
			delay: BlockNumberFor<T>,
		},
	}

	#[pallet::error]
	pub enum Error<T> {
		/// There are too many proxies registered or too many announcements pending.
		TooMany,
		/// Proxy registration not found.
		NotFound,
		/// Sender is not a proxy of the account to be proxied.
		NotProxy,
		/// A call which is incompatible with the proxy type's filter was attempted.
		Unproxyable,
		/// Account is already a proxy.
		Duplicate,
		/// Call may not be made by proxy because it may escalate its privileges.
		NoPermission,
		/// Announcement, if made at all, was made too recently.
		Unannounced,
		/// Cannot add self as proxy.
		NoSelfProxy,
	}

	/// The set of account proxies. Maps the account which has delegated to the accounts
	/// which are being delegated to, together with the amount held on deposit.
	#[pallet::storage]
	#[pallet::getter(fn proxies)]
	pub type Proxies<T: Config> = StorageMap<
		_,
		Twox64Concat,
		T::AccountId,
		(
			BoundedVec<
				ProxyDefinition<T::AccountId, T::ProxyType, BlockNumberFor<T>>,
				T::MaxProxies,
			>,
			BalanceOf<T>,
		),
		ValueQuery,
	>;

	/// The announcements made by the proxy (key).
	#[pallet::storage]
	#[pallet::getter(fn announcements)]
	pub type Announcements<T: Config> = StorageMap<
		_,
		Twox64Concat,
		T::AccountId,
		(
			BoundedVec<Announcement<T::AccountId, CallHashOf<T>, BlockNumberFor<T>>, T::MaxPending>,
			BalanceOf<T>,
		),
		ValueQuery,
	>;
}

impl<T: Config> Pallet<T> {
	/// Calculate the address of an pure account.
	///
	/// - `who`: The spawner account.
	/// - `proxy_type`: The type of the proxy that the sender will be registered as over the
	/// new account. This will almost always be the most permissive `ProxyType` possible to
	/// allow for maximum flexibility.
	/// - `index`: A disambiguation index, in case this is called multiple times in the same
	/// transaction (e.g. with `utility::batch`). Unless you're using `batch` you probably just
	/// want to use `0`.
	/// - `maybe_when`: The block height and extrinsic index of when the pure account was
	/// created. None to use current block height and extrinsic index.
	pub fn pure_account(
		who: &T::AccountId,
		proxy_type: &T::ProxyType,
		index: u16,
		maybe_when: Option<(BlockNumberFor<T>, u32)>,
	) -> T::AccountId {
		let (height, ext_index) = maybe_when.unwrap_or_else(|| {
			(
				system::Pallet::<T>::block_number(),
				system::Pallet::<T>::extrinsic_index().unwrap_or_default(),
			)
		});
		let entropy = (b"modlpy/proxy____", who, height, ext_index, proxy_type, index)
			.using_encoded(blake2_256);
		Decode::decode(&mut TrailingZeroInput::new(entropy.as_ref()))
			.expect("infinite length input; no invalid inputs for type; qed")
	}

	/// Register a proxy account for the delegator that is able to make calls on its behalf.
	///
	/// Parameters:
	/// - `delegator`: The delegator account.
	/// - `delegatee`: The account that the `delegator` would like to make a proxy.
	/// - `proxy_type`: The permissions allowed for this proxy account.
	/// - `delay`: The announcement period required of the initial proxy. Will generally be
	/// zero.
	pub fn add_proxy_delegate(
		delegator: &T::AccountId,
		delegatee: T::AccountId,
		proxy_type: T::ProxyType,
		delay: BlockNumberFor<T>,
	) -> DispatchResult {
		ensure!(delegator != &delegatee, Error::<T>::NoSelfProxy);
		Proxies::<T>::try_mutate(delegator, |(ref mut proxies, ref mut deposit)| {
			let proxy_def = ProxyDefinition {
				delegate: delegatee.clone(),
				proxy_type: proxy_type.clone(),
				delay,
			};
			let i = proxies.binary_search(&proxy_def).err().ok_or(Error::<T>::Duplicate)?;
			proxies.try_insert(i, proxy_def).map_err(|_| Error::<T>::TooMany)?;
			let new_deposit = Self::deposit(proxies.len() as u32);
			if new_deposit > *deposit {
				T::Currency::reserve(delegator, new_deposit - *deposit)?;
			} else if new_deposit < *deposit {
				T::Currency::unreserve(delegator, *deposit - new_deposit);
			}
			*deposit = new_deposit;
			Self::deposit_event(Event::<T>::ProxyAdded {
				delegator: delegator.clone(),
				delegatee,
				proxy_type,
				delay,
			});
			Ok(())
		})
	}

	/// Unregister a proxy account for the delegator.
	///
	/// Parameters:
	/// - `delegator`: The delegator account.
	/// - `delegatee`: The account that the `delegator` would like to make a proxy.
	/// - `proxy_type`: The permissions allowed for this proxy account.
	/// - `delay`: The announcement period required of the initial proxy. Will generally be
	/// zero.
	pub fn remove_proxy_delegate(
		delegator: &T::AccountId,
		delegatee: T::AccountId,
		proxy_type: T::ProxyType,
		delay: BlockNumberFor<T>,
	) -> DispatchResult {
		Proxies::<T>::try_mutate_exists(delegator, |x| {
			let (mut proxies, old_deposit) = x.take().ok_or(Error::<T>::NotFound)?;
			let proxy_def = ProxyDefinition {
				delegate: delegatee.clone(),
				proxy_type: proxy_type.clone(),
				delay,
			};
			let i = proxies.binary_search(&proxy_def).ok().ok_or(Error::<T>::NotFound)?;
			proxies.remove(i);
			let new_deposit = Self::deposit(proxies.len() as u32);
			if new_deposit > old_deposit {
				T::Currency::reserve(delegator, new_deposit - old_deposit)?;
			} else if new_deposit < old_deposit {
				T::Currency::unreserve(delegator, old_deposit - new_deposit);
			}
			if !proxies.is_empty() {
				*x = Some((proxies, new_deposit))
			}
			Self::deposit_event(Event::<T>::ProxyRemoved {
				delegator: delegator.clone(),
				delegatee,
				proxy_type,
				delay,
			});
			Ok(())
		})
	}

	pub fn deposit(num_proxies: u32) -> BalanceOf<T> {
		if num_proxies == 0 {
			Zero::zero()
		} else {
			T::ProxyDepositBase::get() + T::ProxyDepositFactor::get() * num_proxies.into()
		}
	}

	fn rejig_deposit(
		who: &T::AccountId,
		old_deposit: BalanceOf<T>,
		base: BalanceOf<T>,
		factor: BalanceOf<T>,
		len: usize,
	) -> Result<Option<BalanceOf<T>>, DispatchError> {
		let new_deposit =
			if len == 0 { BalanceOf::<T>::zero() } else { base + factor * (len as u32).into() };
		if new_deposit > old_deposit {
			T::Currency::reserve(who, new_deposit - old_deposit)?;
		} else if new_deposit < old_deposit {
			T::Currency::unreserve(who, old_deposit - new_deposit);
		}
		Ok(if len == 0 { None } else { Some(new_deposit) })
	}

	fn edit_announcements<
		F: FnMut(&Announcement<T::AccountId, CallHashOf<T>, BlockNumberFor<T>>) -> bool,
	>(
		delegate: &T::AccountId,
		f: F,
	) -> DispatchResult {
		Announcements::<T>::try_mutate_exists(delegate, |x| {
			let (mut pending, old_deposit) = x.take().ok_or(Error::<T>::NotFound)?;
			let orig_pending_len = pending.len();
			pending.retain(f);
			ensure!(orig_pending_len > pending.len(), Error::<T>::NotFound);
			*x = Self::rejig_deposit(
				delegate,
				old_deposit,
				T::AnnouncementDepositBase::get(),
				T::AnnouncementDepositFactor::get(),
				pending.len(),
			)?
			.map(|deposit| (pending, deposit));
			Ok(())
		})
	}

	pub fn find_proxy(
		real: &T::AccountId,
		delegate: &T::AccountId,
		force_proxy_type: Option<T::ProxyType>,
	) -> Result<ProxyDefinition<T::AccountId, T::ProxyType, BlockNumberFor<T>>, DispatchError> {
		let f = |x: &ProxyDefinition<T::AccountId, T::ProxyType, BlockNumberFor<T>>| -> bool {
			&x.delegate == delegate &&
				force_proxy_type.as_ref().map_or(true, |y| &x.proxy_type == y)
		};
		Ok(Proxies::<T>::get(real).0.into_iter().find(f).ok_or(Error::<T>::NotProxy)?)
	}

	fn do_proxy(
		def: ProxyDefinition<T::AccountId, T::ProxyType, BlockNumberFor<T>>,
		real: T::AccountId,
		call: <T as Config>::RuntimeCall,
	) {
		// This is a freshly authenticated new account, the origin restrictions doesn't apply.
		let mut origin: T::RuntimeOrigin = frame_system::RawOrigin::Signed(real).into();
		origin.add_filter(move |c: &<T as frame_system::Config>::RuntimeCall| {
			let c = <T as Config>::RuntimeCall::from_ref(c);
			// We make sure the proxy call does access this pallet to change modify proxies.
			match c.is_sub_type() {
				// Proxy call cannot add or remove a proxy with more permissions than it already
				// has.
				Some(Call::add_proxy { ref proxy_type, .. }) |
				Some(Call::remove_proxy { ref proxy_type, .. })
					if !def.proxy_type.is_superset(proxy_type) =>
					false,
				// Proxy call cannot remove all proxies or kill pure proxies unless it has full
				// permissions.
				Some(Call::remove_proxies { .. }) | Some(Call::kill_pure { .. })
					if def.proxy_type != T::ProxyType::default() =>
					false,
				_ => def.proxy_type.filter(c),
			}
		});
		let e = call.dispatch(origin);
		Self::deposit_event(Event::ProxyExecuted { result: e.map(|_| ()).map_err(|e| e.error) });
	}

	/// Removes all proxy delegates for a given delegator.
	///
	/// Parameters:
	/// - `delegator`: The delegator account.
	pub fn remove_all_proxy_delegates(delegator: &T::AccountId) {
		let (_, old_deposit) = Proxies::<T>::take(&delegator);
		T::Currency::unreserve(&delegator, old_deposit);
	}
}
