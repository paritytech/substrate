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

use sp_std::prelude::*;
use codec::{Encode, Decode};
use sp_io::hashing::blake2_256;
use sp_runtime::{DispatchResult, traits::{Dispatchable, Zero}};
use sp_runtime::traits::Member;
use frame_support::{
	decl_module, decl_event, decl_error, decl_storage, Parameter, ensure, traits::{
		Get, ReservableCurrency, Currency, InstanceFilter,
		OriginTrait, IsType,
	}, weights::{Weight, GetDispatchInfo, constants::{WEIGHT_PER_MICROS, WEIGHT_PER_NANOS}},
	dispatch::{PostDispatchInfo, IsSubType},
};
use frame_system::{self as system, ensure_signed};

mod tests;
mod benchmarking;

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

pub trait WeightInfo {
	fn proxy(p: u32, ) -> Weight;
	fn add_proxy(p: u32, ) -> Weight;
	fn remove_proxy(p: u32, ) -> Weight;
	fn remove_proxies(p: u32, ) -> Weight;
	fn anonymous(p: u32, ) -> Weight;
	fn kill_anonymous(p: u32, ) -> Weight;
}

impl WeightInfo for () {
	fn proxy(_p: u32, ) -> Weight { 1_000_000_000 }
	fn add_proxy(_p: u32, ) -> Weight { 1_000_000_000 }
	fn remove_proxy(_p: u32, ) -> Weight { 1_000_000_000 }
	fn remove_proxies(_p: u32, ) -> Weight { 1_000_000_000 }
	fn anonymous(_p: u32, ) -> Weight { 1_000_000_000 }
	fn kill_anonymous(_p: u32, ) -> Weight { 1_000_000_000 }
}

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
}

decl_storage! {
	trait Store for Module<T: Trait> as Proxy {
		/// The set of account proxies. Maps the account which has delegated to the accounts
		/// which are being delegated to, together with the amount held on deposit.
		pub Proxies: map hasher(twox_64_concat) T::AccountId => (Vec<(T::AccountId, T::ProxyType)>, BalanceOf<T>);
	}
}

decl_error! {
	pub enum Error for Module<T: Trait> {
		/// There are too many proxies registered.
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
	}
}

decl_event! {
	/// Events type.
	pub enum Event<T> where
		AccountId = <T as frame_system::Trait>::AccountId,
		ProxyType = <T as Trait>::ProxyType
	{
		/// A proxy was executed correctly, with the given [result].
		ProxyExecuted(DispatchResult),
		/// Anonymous account has been created by new proxy with given
		/// disambiguation index and proxy type. [anonymous, who, proxy_type, disambiguation_index]
		AnonymousCreated(AccountId, AccountId, ProxyType, u16),
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

		/// Dispatch the given `call` from an account that the sender is authorised for through
		/// `add_proxy`.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// Parameters:
		/// - `real`: The account that the proxy will make a call on behalf of.
		/// - `force_proxy_type`: Specify the exact proxy type to be used and checked for this call.
		/// - `call`: The call to be made by the `real` account.
		///
		/// # <weight>
		/// P is the number of proxies the user has
		/// - Base weight: 19.87 + .141 * P µs
		/// - DB weight: 1 storage read.
		/// - Plus the weight of the `call`
		/// # </weight>
		#[weight = {
			let di = call.get_dispatch_info();
			(T::DbWeight::get().reads(1)
				.saturating_add(di.weight)
				.saturating_add(20 * WEIGHT_PER_MICROS)
				.saturating_add((140 * WEIGHT_PER_NANOS).saturating_mul(T::MaxProxies::get().into())),
			di.class)
		}]
		fn proxy(origin,
			real: T::AccountId,
			force_proxy_type: Option<T::ProxyType>,
			call: Box<<T as Trait>::Call>
		) {
			let who = ensure_signed(origin)?;
			let (_, proxy_type) = Proxies::<T>::get(&real).0.into_iter()
				.find(|x| &x.0 == &who && force_proxy_type.as_ref().map_or(true, |y| &x.1 == y))
				.ok_or(Error::<T>::NotProxy)?;

			// This is a freshly authenticated new account, the origin restrictions doesn't apply.
			let mut origin: T::Origin = frame_system::RawOrigin::Signed(real).into();
			origin.add_filter(move |c: &<T as frame_system::Trait>::Call| {
				let c = <T as Trait>::Call::from_ref(c);
				match c.is_sub_type() {
					Some(Call::add_proxy(_, ref pt)) | Some(Call::remove_proxy(_, ref pt))
						if !proxy_type.is_superset(&pt) => false,
					Some(Call::remove_proxies(..)) | Some(Call::kill_anonymous(..))
					    if proxy_type != T::ProxyType::default() => false,
					_ => proxy_type.filter(c)
				}
			});
			let e = call.dispatch(origin);
			Self::deposit_event(RawEvent::ProxyExecuted(e.map(|_| ()).map_err(|e| e.error)));
		}

		/// Register a proxy account for the sender that is able to make calls on its behalf.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// Parameters:
		/// - `proxy`: The account that the `caller` would like to make a proxy.
		/// - `proxy_type`: The permissions allowed for this proxy account.
		///
		/// # <weight>
		/// P is the number of proxies the user has
		/// - Base weight: 17.48 + .176 * P µs
		/// - DB weight: 1 storage read and write.
		/// # </weight>
		#[weight = T::DbWeight::get().reads_writes(1, 1)
			.saturating_add(18 * WEIGHT_PER_MICROS)
			.saturating_add((200 * WEIGHT_PER_NANOS).saturating_mul(T::MaxProxies::get().into()))
		]
		fn add_proxy(origin, proxy: T::AccountId, proxy_type: T::ProxyType) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Proxies::<T>::try_mutate(&who, |(ref mut proxies, ref mut deposit)| {
				ensure!(proxies.len() < T::MaxProxies::get() as usize, Error::<T>::TooMany);
				let typed_proxy = (proxy, proxy_type);
				let i = proxies.binary_search(&typed_proxy).err().ok_or(Error::<T>::Duplicate)?;
				proxies.insert(i, typed_proxy);
				let new_deposit = T::ProxyDepositBase::get()
					+ T::ProxyDepositFactor::get() * (proxies.len() as u32).into();
				if new_deposit > *deposit {
					T::Currency::reserve(&who, new_deposit - *deposit)?;
				} else if new_deposit < *deposit {
					T::Currency::unreserve(&who, *deposit - new_deposit);
				}
				*deposit = new_deposit;
				Ok(())
			})
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
		/// P is the number of proxies the user has
		/// - Base weight: 14.37 + .164 * P µs
		/// - DB weight: 1 storage read and write.
		/// # </weight>
		#[weight = T::DbWeight::get().reads_writes(1, 1)
			.saturating_add(14 * WEIGHT_PER_MICROS)
			.saturating_add((160 * WEIGHT_PER_NANOS).saturating_mul(T::MaxProxies::get().into()))
		]
		fn remove_proxy(origin, proxy: T::AccountId, proxy_type: T::ProxyType) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Proxies::<T>::try_mutate_exists(&who, |x| {
				let (mut proxies, old_deposit) = x.take().ok_or(Error::<T>::NotFound)?;
				let typed_proxy = (proxy, proxy_type);
				let i = proxies.binary_search(&typed_proxy).ok().ok_or(Error::<T>::NotFound)?;
				proxies.remove(i);
				let new_deposit = if proxies.is_empty() {
					BalanceOf::<T>::zero()
				} else {
					T::ProxyDepositBase::get() + T::ProxyDepositFactor::get() * (proxies.len() as u32).into()
				};
				if new_deposit > old_deposit {
					T::Currency::reserve(&who, new_deposit - old_deposit)?;
				} else if new_deposit < old_deposit {
					T::Currency::unreserve(&who, old_deposit - new_deposit);
				}
				if !proxies.is_empty() {
					*x = Some((proxies, new_deposit))
				}
				Ok(())
			})
		}

		/// Unregister all proxy accounts for the sender.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// WARNING: This may be called on accounts created by `anonymous`, however if done, then
		/// the unreserved fees will be inaccessible. **All access to this account will be lost.**
		///
		/// # <weight>
		/// P is the number of proxies the user has
		/// - Base weight: 13.73 + .129 * P µs
		/// - DB weight: 1 storage read and write.
		/// # </weight>
		#[weight = T::DbWeight::get().reads_writes(1, 1)
			.saturating_add(14 * WEIGHT_PER_MICROS)
			.saturating_add((130 * WEIGHT_PER_NANOS).saturating_mul(T::MaxProxies::get().into()))
		]
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
		///
		/// Fails with `Duplicate` if this has already been called in this transaction, from the
		/// same sender, with the same parameters.
		///
		/// Fails if there are insufficient funds to pay for deposit.
		///
		/// # <weight>
		/// P is the number of proxies the user has
		/// - Base weight: 36.48 + .039 * P µs
		/// - DB weight: 1 storage read and write.
		/// # </weight>
		#[weight = T::DbWeight::get().reads_writes(1, 1)
			.saturating_add(36 * WEIGHT_PER_MICROS)
			.saturating_add((40 * WEIGHT_PER_NANOS).saturating_mul(T::MaxProxies::get().into()))
		]
		fn anonymous(origin, proxy_type: T::ProxyType, index: u16) {
			let who = ensure_signed(origin)?;

			let anonymous = Self::anonymous_account(&who, &proxy_type, index, None);
			ensure!(!Proxies::<T>::contains_key(&anonymous), Error::<T>::Duplicate);
			let deposit = T::ProxyDepositBase::get() + T::ProxyDepositFactor::get();
			T::Currency::reserve(&who, deposit)?;
			Proxies::<T>::insert(&anonymous, (vec![(who.clone(), proxy_type.clone())], deposit));
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
		/// P is the number of proxies the user has
		/// - Base weight: 15.65 + .137 * P µs
		/// - DB weight: 1 storage read and write.
		/// # </weight>
		#[weight = T::DbWeight::get().reads_writes(1, 1)
			.saturating_add(15 * WEIGHT_PER_MICROS)
			.saturating_add((140 * WEIGHT_PER_NANOS).saturating_mul(T::MaxProxies::get().into()))
		]
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
	}
}

impl<T: Trait> Module<T> {
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
}
