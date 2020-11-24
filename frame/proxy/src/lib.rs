// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

//! # Proxy Module
//! A module allowing accounts to give permission to other accounts to dispatch types of calls from
//! their signed origin.
//!
//! The accounts to which permission is delegated may be requied to announce the action that they
//! wish to execute some duration prior to execution happens. In this case, the target account may
//! reject the announcement and in doing so, veto the execution.
//!
//! - [`proxy::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//!
//! ## Overview
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! [`Call`]: ./enum.Call.html
//! [`Trait`]: ./trait.Trait.html

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

mod tests;
mod benchmarking;
pub mod weights;

use sp_std::prelude::*;
use codec::{Encode, Decode};
use sp_io::hashing::blake2_256;
use sp_runtime::{DispatchResult, traits::{Dispatchable, Zero, Hash, Member, Saturating}};
use frame_support::{
	decl_module, decl_event, decl_error, decl_storage, Parameter, ensure, RuntimeDebug, traits::{
		Get, ReservableCurrency, Currency, InstanceFilter, OriginTrait, IsType, IsSubType,
	}, weights::{Weight, GetDispatchInfo}, dispatch::PostDispatchInfo, storage::IterableStorageMap,
};
use frame_system::{self as system, ensure_signed};
use frame_support::dispatch::DispatchError;
pub use weights::WeightInfo;

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

/// Configuration trait.
pub trait Trait: frame_system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;

	/// The overarching call type.
	type Call: Parameter + Dispatchable<Origin=Self::Origin, PostInfo=PostDispatchInfo>
		+ GetDispatchInfo + From<frame_system::Call<Self>> + IsSubType<Call<Self>>
		+ IsType<<Self as frame_system::Trait>::Call>;

	/// The currency mechanism.
	type Currency: ReservableCurrency<Self::AccountId>;

	/// A kind of proxy; specified with the proxy and passed in to the `IsProxyable` fitler.
	/// The instance filter determines whether a given call may be proxied under this type.
	///
	/// IMPORTANT: `Default` must be provided and MUST BE the the *most permissive* value.
	type ProxyType: Parameter + Member + Ord + PartialOrd + InstanceFilter<<Self as Trait>::Call>
		+ Default;

	/// The base amount of currency needed to reserve for creating a proxy.
	///
	/// This is held for an additional storage item whose value size is
	/// `sizeof(Balance)` bytes and whose key size is `sizeof(AccountId)` bytes.
	type ProxyDepositBase: Get<BalanceOf<Self>>;

	/// The amount of currency needed per proxy added.
	///
	/// This is held for adding 32 bytes plus an instance of `ProxyType` more into a pre-existing
	/// storage value.
	type ProxyDepositFactor: Get<BalanceOf<Self>>;

	/// The maximum amount of proxies allowed for a single account.
	type MaxProxies: Get<u16>;

	/// Weight information for extrinsics in this pallet.
	type WeightInfo: WeightInfo;

	/// The maximum amount of time-delayed announcements that are allowed to be pending.
	type MaxPending: Get<u32>;

	/// The type of hash used for hashing the call.
	type CallHasher: Hash;

	/// The base amount of currency needed to reserve for creating an announcement.
	///
	/// This is held when a new storage item holding a `Balance` is created (typically 16 bytes).
	type AnnouncementDepositBase: Get<BalanceOf<Self>>;

	/// The amount of currency needed per announcement made.
	///
	/// This is held for adding an `AccountId`, `Hash` and `BlockNumber` (typically 68 bytes)
	/// into a pre-existing storage value.
	type AnnouncementDepositFactor: Get<BalanceOf<Self>>;
}

/// The parameters under which a particular account has a proxy relationship with some other
/// account.
#[derive(Encode, Decode, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, RuntimeDebug)]
pub struct ProxyDefinition<AccountId, ProxyType, BlockNumber> {
	/// The account which may act on behalf of another.
	delegate: AccountId,
	/// A value defining the subset of calls that it is allowed to make.
	proxy_type: ProxyType,
	/// The number of blocks that an announcement must be in place for before the corresponding call
	/// may be dispatched. If zero, then no announcement is needed.
	delay: BlockNumber,
}

/// Details surrounding a specific instance of an announcement to make a call.
#[derive(Encode, Decode, Clone, Copy, Eq, PartialEq, RuntimeDebug)]
pub struct Announcement<AccountId, Hash, BlockNumber> {
	/// The account which made the announcement.
	real: AccountId,
	/// The hash of the call to be made.
	call_hash: Hash,
	/// The height at which the announcement was made.
	height: BlockNumber,
}

type CallHashOf<T> = <<T as Trait>::CallHasher as Hash>::Output;

decl_storage! {
	trait Store for Module<T: Trait> as Proxy {
		/// The set of account proxies. Maps the account which has delegated to the accounts
		/// which are being delegated to, together with the amount held on deposit.
		pub Proxies get(fn proxies): map hasher(twox_64_concat) T::AccountId
			=> (Vec<ProxyDefinition<T::AccountId, T::ProxyType, T::BlockNumber>>, BalanceOf<T>);

		/// The announcements made by the proxy (key).
		pub Announcements get(fn announcements): map hasher(twox_64_concat) T::AccountId
			=> (Vec<Announcement<T::AccountId, CallHashOf<T>, T::BlockNumber>>, BalanceOf<T>);
	}
}

decl_error! {
	pub enum Error for Module<T: Trait> {
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
	}
}

decl_event! {
	/// Events type.
	pub enum Event<T> where
		AccountId = <T as frame_system::Trait>::AccountId,
		ProxyType = <T as Trait>::ProxyType,
		Hash = CallHashOf<T>,
	{
		/// A proxy was executed correctly, with the given \[result\].
		ProxyExecuted(DispatchResult),
		/// Anonymous account has been created by new proxy with given
		/// disambiguation index and proxy type. \[anonymous, who, proxy_type, disambiguation_index\]
		AnonymousCreated(AccountId, AccountId, ProxyType, u16),
		/// An announcement was placed to make a call in the future. \[real, proxy, call_hash\]
		Announced(AccountId, AccountId, Hash),
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		/// Deposit one of this module's events by using the default implementation.
		fn deposit_event() = default;

		/// The base amount of currency needed to reserve for creating a proxy.
		const ProxyDepositBase: BalanceOf<T> = T::ProxyDepositBase::get();

		/// The amount of currency needed per proxy added.
		const ProxyDepositFactor: BalanceOf<T> = T::ProxyDepositFactor::get();

		/// The maximum amount of proxies allowed for a single account.
		const MaxProxies: u16 = T::MaxProxies::get();

		/// `MaxPending` metadata shadow.
		const MaxPending: u32 = T::MaxPending::get();

		/// `AnnouncementDepositBase` metadata shadow.
		const AnnouncementDepositBase: BalanceOf<T> = T::AnnouncementDepositBase::get();

		/// `AnnouncementDepositFactor` metadata shadow.
		const AnnouncementDepositFactor: BalanceOf<T> = T::AnnouncementDepositFactor::get();

		/// Dispatch the given `call` from an account that the sender is authorised for through
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
		///
		/// # <weight>
		/// Weight is a function of the number of proxies the user has (P).
		/// # </weight>
		#[weight = {
			let di = call.get_dispatch_info();
			(T::WeightInfo::proxy(T::MaxProxies::get().into())
				.saturating_add(di.weight)
				 // AccountData for inner call origin accountdata.
				.saturating_add(T::DbWeight::get().reads_writes(1, 1)),
			di.class)
		}]
		fn proxy(origin,
			real: T::AccountId,
			force_proxy_type: Option<T::ProxyType>,
			call: Box<<T as Trait>::Call>,
		) {
			let who = ensure_signed(origin)?;
			let def = Self::find_proxy(&real, &who, force_proxy_type)?;
			ensure!(def.delay.is_zero(), Error::<T>::Unannounced);

			Self::do_proxy(def, real, *call);
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
		///
		/// # <weight>
		/// Weight is a function of the number of proxies the user has (P).
		/// # </weight>
		#[weight = T::WeightInfo::add_proxy(T::MaxProxies::get().into())]
		fn add_proxy(origin,
			delegate: T::AccountId,
			proxy_type: T::ProxyType,
			delay: T::BlockNumber,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::add_proxy_delegate(&who, delegate, proxy_type, delay)
		}

		/// Unregister a proxy account for the sender.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// Parameters:
		/// - `proxy`: The account that the `caller` would like to remove as a proxy.
		/// - `proxy_type`: The permissions currently enabled for the removed proxy account.
		///
		/// # <weight>
		/// Weight is a function of the number of proxies the user has (P).
		/// # </weight>
		#[weight = T::WeightInfo::remove_proxy(T::MaxProxies::get().into())]
		fn remove_proxy(origin,
			delegate: T::AccountId,
			proxy_type: T::ProxyType,
			delay: T::BlockNumber,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::remove_proxy_delegate(&who, delegate, proxy_type, delay)
		}

		/// Unregister all proxy accounts for the sender.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// WARNING: This may be called on accounts created by `anonymous`, however if done, then
		/// the unreserved fees will be inaccessible. **All access to this account will be lost.**
		///
		/// # <weight>
		/// Weight is a function of the number of proxies the user has (P).
		/// # </weight>
		#[weight = T::WeightInfo::remove_proxies(T::MaxProxies::get().into())]
		fn remove_proxies(origin) {
			let who = ensure_signed(origin)?;
			let (_, old_deposit) = Proxies::<T>::take(&who);
			T::Currency::unreserve(&who, old_deposit);
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
		///
		/// # <weight>
		/// Weight is a function of the number of proxies the user has (P).
		/// # </weight>
		/// TODO: Might be over counting 1 read
		#[weight = T::WeightInfo::anonymous(T::MaxProxies::get().into())]
		fn anonymous(origin, proxy_type: T::ProxyType, delay: T::BlockNumber, index: u16) {
			let who = ensure_signed(origin)?;

			let anonymous = Self::anonymous_account(&who, &proxy_type, index, None);
			ensure!(!Proxies::<T>::contains_key(&anonymous), Error::<T>::Duplicate);
			let deposit = T::ProxyDepositBase::get() + T::ProxyDepositFactor::get();
			T::Currency::reserve(&who, deposit)?;
			let proxy_def = ProxyDefinition {
				delegate: who.clone(),
				proxy_type: proxy_type.clone(),
				delay,
			};
			Proxies::<T>::insert(&anonymous, (vec![proxy_def], deposit));
			Self::deposit_event(RawEvent::AnonymousCreated(anonymous, who, proxy_type, index));
		}

		/// Removes a previously spawned anonymous proxy.
		///
		/// WARNING: **All access to this account will be lost.** Any funds held in it will be
		/// inaccessible.
		///
		/// Requires a `Signed` origin, and the sender account must have been created by a call to
		/// `anonymous` with corresponding parameters.
		///
		/// - `spawner`: The account that originally called `anonymous` to create this account.
		/// - `index`: The disambiguation index originally passed to `anonymous`. Probably `0`.
		/// - `proxy_type`: The proxy type originally passed to `anonymous`.
		/// - `height`: The height of the chain when the call to `anonymous` was processed.
		/// - `ext_index`: The extrinsic index in which the call to `anonymous` was processed.
		///
		/// Fails with `NoPermission` in case the caller is not a previously created anonymous
		/// account whose `anonymous` call has corresponding parameters.
		///
		/// # <weight>
		/// Weight is a function of the number of proxies the user has (P).
		/// # </weight>
		#[weight = T::WeightInfo::kill_anonymous(T::MaxProxies::get().into())]
		fn kill_anonymous(origin,
			spawner: T::AccountId,
			proxy_type: T::ProxyType,
			index: u16,
			#[compact] height: T::BlockNumber,
			#[compact] ext_index: u32,
		) {
			let who = ensure_signed(origin)?;

			let when = (height, ext_index);
			let proxy = Self::anonymous_account(&spawner, &proxy_type, index, Some(when));
			ensure!(proxy == who, Error::<T>::NoPermission);

			let (_, deposit) = Proxies::<T>::take(&who);
			T::Currency::unreserve(&spawner, deposit);
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
		///
		/// # <weight>
		/// Weight is a function of:
		/// - A: the number of announcements made.
		/// - P: the number of proxies the user has.
		/// # </weight>
		#[weight = T::WeightInfo::announce(T::MaxPending::get(), T::MaxProxies::get().into())]
		fn announce(origin, real: T::AccountId, call_hash: CallHashOf<T>) {
			let who = ensure_signed(origin)?;
			Proxies::<T>::get(&real).0.into_iter()
				.find(|x| &x.delegate == &who)
				.ok_or(Error::<T>::NotProxy)?;

			let announcement = Announcement {
				real: real.clone(),
				call_hash: call_hash.clone(),
				height: system::Module::<T>::block_number(),
			};

			Announcements::<T>::try_mutate(&who, |(ref mut pending, ref mut deposit)| {
				ensure!(pending.len() < T::MaxPending::get() as usize, Error::<T>::TooMany);
				pending.push(announcement);
				Self::rejig_deposit(
					&who,
					*deposit,
					T::AnnouncementDepositBase::get(),
					T::AnnouncementDepositFactor::get(),
					pending.len(),
				).map(|d| d.expect("Just pushed; pending.len() > 0; rejig_deposit returns Some; qed"))
				.map(|d| *deposit = d)
			})?;
			Self::deposit_event(RawEvent::Announced(real, who, call_hash));
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
		///
		/// # <weight>
		/// Weight is a function of:
		/// - A: the number of announcements made.
		/// - P: the number of proxies the user has.
		/// # </weight>
		#[weight = T::WeightInfo::remove_announcement(T::MaxPending::get(), T::MaxProxies::get().into())]
		fn remove_announcement(origin, real: T::AccountId, call_hash: CallHashOf<T>) {
			let who = ensure_signed(origin)?;
			Self::edit_announcements(&who, |ann| ann.real != real || ann.call_hash != call_hash)?;
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
		///
		/// # <weight>
		/// Weight is a function of:
		/// - A: the number of announcements made.
		/// - P: the number of proxies the user has.
		/// # </weight>
		#[weight = T::WeightInfo::reject_announcement(T::MaxPending::get(), T::MaxProxies::get().into())]
		fn reject_announcement(origin, delegate: T::AccountId, call_hash: CallHashOf<T>) {
			let who = ensure_signed(origin)?;
			Self::edit_announcements(&delegate, |ann| ann.real != who || ann.call_hash != call_hash)?;
		}

		/// Dispatch the given `call` from an account that the sender is authorised for through
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
		///
		/// # <weight>
		/// Weight is a function of:
		/// - A: the number of announcements made.
		/// - P: the number of proxies the user has.
		/// # </weight>
		#[weight = {
			let di = call.get_dispatch_info();
			(T::WeightInfo::proxy_announced(T::MaxPending::get(), T::MaxProxies::get().into())
				.saturating_add(di.weight)
				 // AccountData for inner call origin accountdata.
				.saturating_add(T::DbWeight::get().reads_writes(1, 1)),
			di.class)
		}]
		fn proxy_announced(origin,
			delegate: T::AccountId,
			real: T::AccountId,
			force_proxy_type: Option<T::ProxyType>,
			call: Box<<T as Trait>::Call>,
		) {
			ensure_signed(origin)?;
			let def = Self::find_proxy(&real, &delegate, force_proxy_type)?;

			let call_hash = T::CallHasher::hash_of(&call);
			let now = system::Module::<T>::block_number();
			Self::edit_announcements(&delegate, |ann|
				ann.real != real || ann.call_hash != call_hash || now.saturating_sub(ann.height) < def.delay
			).map_err(|_| Error::<T>::Unannounced)?;

			Self::do_proxy(def, real, *call);
		}
	}
}

impl<T: Trait> Module<T> {

	/// Calculate the address of an anonymous account.
	///
	/// - `who`: The spawner account.
	/// - `proxy_type`: The type of the proxy that the sender will be registered as over the
	/// new account. This will almost always be the most permissive `ProxyType` possible to
	/// allow for maximum flexibility.
	/// - `index`: A disambiguation index, in case this is called multiple times in the same
	/// transaction (e.g. with `utility::batch`). Unless you're using `batch` you probably just
	/// want to use `0`.
	/// - `maybe_when`: The block height and extrinsic index of when the anonymous account was
	/// created. None to use current block height and extrinsic index.
	pub fn anonymous_account(
		who: &T::AccountId,
		proxy_type: &T::ProxyType,
		index: u16,
		maybe_when: Option<(T::BlockNumber, u32)>,
	) -> T::AccountId {
		let (height, ext_index) = maybe_when.unwrap_or_else(|| (
			system::Module::<T>::block_number(),
			system::Module::<T>::extrinsic_index().unwrap_or_default()
		));
		let entropy = (b"modlpy/proxy____", who, height, ext_index, proxy_type, index)
			.using_encoded(blake2_256);
		T::AccountId::decode(&mut &entropy[..]).unwrap_or_default()
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
		delay: T::BlockNumber,
	) -> DispatchResult {
		Proxies::<T>::try_mutate(delegator, |(ref mut proxies, ref mut deposit)| {
			ensure!(proxies.len() < T::MaxProxies::get() as usize, Error::<T>::TooMany);
			let proxy_def = ProxyDefinition { delegate: delegatee, proxy_type, delay };
			let i = proxies.binary_search(&proxy_def).err().ok_or(Error::<T>::Duplicate)?;
			proxies.insert(i, proxy_def);
			let new_deposit = Self::deposit(proxies.len() as u32);
			if new_deposit > *deposit {
				T::Currency::reserve(delegator, new_deposit - *deposit)?;
			} else if new_deposit < *deposit {
				T::Currency::unreserve(delegator, *deposit - new_deposit);
			}
			*deposit = new_deposit;
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
		delay: T::BlockNumber,
	) -> DispatchResult {
		Proxies::<T>::try_mutate_exists(delegator, |x| {
			let (mut proxies, old_deposit) = x.take().ok_or(Error::<T>::NotFound)?;
			let proxy_def = ProxyDefinition { delegate: delegatee, proxy_type, delay };
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
		let new_deposit = if len == 0 {
			BalanceOf::<T>::zero()
		} else {
			base + factor * (len as u32).into()
		};
		if new_deposit > old_deposit {
			T::Currency::reserve(&who, new_deposit - old_deposit)?;
		} else if new_deposit < old_deposit {
			T::Currency::unreserve(&who, old_deposit - new_deposit);
		}
		Ok(if len == 0 {
			None
		} else {
			Some(new_deposit)
		})
	}

	fn edit_announcements<
		F: FnMut(&Announcement<T::AccountId, CallHashOf<T>, T::BlockNumber>) -> bool
	>(delegate: &T::AccountId, f: F) -> DispatchResult {
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
			)?.map(|deposit| (pending, deposit));
			Ok(())
		})
	}

	fn find_proxy(
		real: &T::AccountId,
		delegate: &T::AccountId,
		force_proxy_type: Option<T::ProxyType>,
	) -> Result<ProxyDefinition<T::AccountId, T::ProxyType, T::BlockNumber>, DispatchError> {
		let f = |x: &ProxyDefinition<T::AccountId, T::ProxyType, T::BlockNumber>| -> bool {
			&x.delegate == delegate && force_proxy_type.as_ref().map_or(true, |y| &x.proxy_type == y)
		};
		Ok(Proxies::<T>::get(real).0.into_iter().find(f).ok_or(Error::<T>::NotProxy)?)
	}

	fn do_proxy(
		def: ProxyDefinition<T::AccountId, T::ProxyType, T::BlockNumber>,
		real: T::AccountId,
		call: <T as Trait>::Call,
	) {
		// This is a freshly authenticated new account, the origin restrictions doesn't apply.
		let mut origin: T::Origin = frame_system::RawOrigin::Signed(real).into();
		origin.add_filter(move |c: &<T as frame_system::Trait>::Call| {
			let c = <T as Trait>::Call::from_ref(c);
			// We make sure the proxy call does access this pallet to change modify proxies.
			match c.is_sub_type() {
				// Proxy call cannot add or remove a proxy with more permissions than it already has.
				Some(Call::add_proxy(_, ref pt, _)) | Some(Call::remove_proxy(_, ref pt, _))
					if !def.proxy_type.is_superset(&pt) => false,
				// Proxy call cannot remove all proxies or kill anonymous proxies unless it has full permissions.
				Some(Call::remove_proxies(..)) | Some(Call::kill_anonymous(..))
					if def.proxy_type != T::ProxyType::default() => false,
				_ => def.proxy_type.filter(c)
			}
		});
		let e = call.dispatch(origin);
		Self::deposit_event(RawEvent::ProxyExecuted(e.map(|_| ()).map_err(|e| e.error)));
	}
}

/// Migration utilities for upgrading the Proxy pallet between its different versions.
pub mod migration {
	use super::*;

	/// Migration code for https://github.com/paritytech/substrate/pull/6770
	///
	/// Details: This migration was introduced between Substrate 2.0-RC6 and Substrate 2.0 releases.
	/// Before this migration, the `Proxies` storage item used a tuple of `AccountId` and
	/// `ProxyType` to represent the proxy definition. After #6770, we switched to use a struct
	/// `ProxyDefinition` which additionally included a `BlockNumber` delay value. This function,
	/// simply takes any existing proxies using the old tuple format, and migrates it to the new
	/// struct by setting the delay to zero.
	pub fn migrate_to_time_delayed_proxies<T: Trait>() -> Weight {
		Proxies::<T>::translate::<(Vec<(T::AccountId, T::ProxyType)>, BalanceOf<T>), _>(
			|_, (targets, deposit)| Some((
				targets.into_iter()
					.map(|(a, t)| ProxyDefinition {
						delegate: a,
						proxy_type: t,
						delay: Zero::zero(),
					})
					.collect::<Vec<_>>(),
				deposit,
			))
		);
		T::MaximumBlockWeight::get()
	}
}
