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
use frame_support::{decl_module, decl_event, decl_error, decl_storage, Parameter, ensure};
use frame_support::{
	traits::{Get, ReservableCurrency, Currency, Filter, InstanceFilter},
	weights::{GetDispatchInfo, constants::{WEIGHT_PER_MICROS, WEIGHT_PER_NANOS}},
	dispatch::{PostDispatchInfo, IsSubType},
};
use frame_system::{self as system, ensure_signed};
use sp_runtime::{DispatchResult, traits::{Dispatchable, Zero}};
use sp_runtime::traits::Member;

mod tests;
mod benchmarking;

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

/// Configuration trait.
pub trait Trait: frame_system::Trait {
	/// The overarching event type.
	type Event: From<Event> + Into<<Self as frame_system::Trait>::Event>;

	/// The overarching call type.
	type Call: Parameter + Dispatchable<Origin=Self::Origin, PostInfo=PostDispatchInfo>
		+ GetDispatchInfo + From<frame_system::Call<Self>> + IsSubType<Module<Self>, Self>;

	/// The currency mechanism.
	type Currency: ReservableCurrency<Self::AccountId>;

	/// Is a given call compatible with the proxying subsystem?
	type IsCallable: Filter<<Self as Trait>::Call>;

	/// A kind of proxy; specified with the proxy and passed in to the `IsProxyable` fitler.
	/// The instance filter determines whether a given call may be proxied under this type.
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
		/// A call with a `false` `IsCallable` filter was attempted.
		Uncallable,
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
	pub enum Event {
		/// A proxy was executed correctly, with the given result.
		ProxyExecuted(DispatchResult),
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		/// Deposit one of this module's events by using the default implementation.
		fn deposit_event() = default;

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
			ensure!(T::IsCallable::filter(&call), Error::<T>::Uncallable);
			let (_, proxy_type) = Proxies::<T>::get(&real).0.into_iter()
				.find(|x| &x.0 == &who && force_proxy_type.as_ref().map_or(true, |y| &x.1 == y))
				.ok_or(Error::<T>::NotProxy)?;
			match call.is_sub_type() {
				Some(Call::add_proxy(_, ref pt)) | Some(Call::remove_proxy(_, ref pt)) =>
					ensure!(&proxy_type == pt, Error::<T>::NoPermission),
				_ => (),
			}
			ensure!(proxy_type.filter(&call), Error::<T>::Unproxyable);
			let e = call.dispatch(frame_system::RawOrigin::Signed(real).into());
			Self::deposit_event(Event::ProxyExecuted(e.map(|_| ()).map_err(|e| e.error)));
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
	}
}
