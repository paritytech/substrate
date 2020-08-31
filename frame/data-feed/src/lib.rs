// Copyright 2020 Parity Technologies (UK) Ltd.
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
// along with Substrate. If not, see <http://www.gnu.org/licenses/>.

//! # DataFeed Module
//!
//! The DataFeed module provides a way to feed data from external world to runtime.
//! This module is designed for a general data feed purpose, to make feeding data a
//! User-friendly service for those who do not have in-depth knowledge of the
//! offchain worker. With this pallet, you can fetch the offchain data and feed it
//! back onto blockchain and modify some specific runtime storage.
//!
//! - [`data_feed::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//! - [`Module`](./struct.Module.html)
//!
//! ## Overview
//!
//! In this data-feed pallet, we can specify a very limited set of storage keys and
//!data providers (also very limited set). Only a permitted account (listed in thethe
//! provider set) is allowed to feed data onto the chain.
//!
//! These fetched data will be used to modify the value under the specified storage
//! key after some operations.
//! The DataFeed module provides functions for:
//!
//! - Setting a collections of data providers(AccountId).
//! - Setting StorageKey to a limited list.
//! - Feeding data from a call from outside.
//! - Providing Sum and Average type to calculate feeded data, the computational process would be
//! called at intervals of blocks by setting.
//! - Using offchain worker to submit data
//!
//! ### Terminology
//!
//! - **StorageKey:** It's a key of a storage in runtime, which also be the identifier of a feeded
//! data. Some one feed data should provide `StorageKey`. And normally, `StorageKey` would be the
//! hashed key of a Storage like `Twox128(Example)++Twox128(Dummy)`(which is depends on marco
//! `decl_storage!`) or an unhashed key `:StorageName:`(which is depends on marco `parameter_types!`)
//!
//! - **DataType:** Due data feed module do not know what data it would receive, so that this module
//! could only limit some type data. Thus we decide to use U128 to stand for all integer data and use
//! FixedU128 to stand for all non-interger. The data from outside would parse into `DataType`, and
//! stored in an limit ring buffer for a data provider.
//!
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! * `register_storage_key` - Register a storage key whose value can be modified within
//!     data feed pallet.
//! * `remove_storage_key` - Remove a storage key whose value can no longer be touched by
//!    data feed pallet.
//! * `set_url` - Set a url under a specific key whose value can be querried from
//! * `set_offchain_period` - Set a period for a specific key that the offchain would be called for
//!    the period interval. Note only set a period for a key, the offchain would submit related data,
//!    otherwise, the offchain would not work for this key.
//! * `feed_data` - Submit a piece of data on chain with a signed transaction
//! * `add_provider` - Add a whitelisted account that is able to submit data on chain
//! * `remove_provider` - An account removed from the whitelist still can submit data on chain
//!     but his data is no longer valid when calculating.
//!
//! ## Usage
//!
//! The following examples show how to use the DataFeed module in your custom module.
//!
//! ### Examples from the FRAME
//!
//! The Example `template module` uses two way to get the datas which are feeded by this data-feed module
//! we use template module as the example to show how to use data-feed
//! 1. first way: the storage defined in template module.
//! Note: when calculate exceed data limit, data-feed would delete this storage. Using this way,
//! developer could get `None` from the storage. (But due to NumberType is u128, rarely case would
//! meet this situation)
//! ```nocompile
//! // in template module:
//! use pallet_data_feed::DataType;
//! pub trait Trait: frame_system::Trait {
//! 	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
//! }
//! decl_storage! {
//! 	trait Store for Module<T: Trait> as TemplateModule {
//!         // we define a storage which is type from data_feed module
//! 		pub Something get(fn something): Option<DataType>;
//! 	}
//! }
//! // in data-feed module
//! // 1. first need to register DataProvider.
//! // 2. then need to register StorageKey:
//! //      1. use extrinsic to call `register_storage_key`
//! //      2. the param: `key: StorageKey` is a bytes from template module using
//! //            `template::Something::hashed_key()`
//! //      3. the param: `info: FeededDataInfo<T::BlockNumber>` would contain operation type, schedule block interval and so no.
//! // 3. use offchain worker or a program beside the chain to submit `feed_data` extrinsic to feed data.
//! // 4. template module could use `Something` to get data and use.
//! ```
//! 2. second way: the storage defined in runtime
//! Note: when calculate exceed data limit, data-feed would delete this storage. However macro
//! `parameter_types` would return default value for this case, so using this way, we suggest
//! developer could judge by whether the data is default to decide other thing.
//! (But due to NumberType is u128, rarely case would meet this situation)
//! ```nocompile
//! // in template module:
//! pub trait Trait: frame_system::Trait {
//! 	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
//!     type Data: Get<u32>; // for example template module need a data in u32 type
//! }
//! // in runtime/src/lib.rs:
//! // this just a example, developer could define the storage in any place.
//! parameter_types! {
//!     pub storage StorageArgument: pallet_data_feed::DataType = pallet_data_feed::DataType::U128(0);
//! }
//! pub struct SimpleDataFeedGet;
//! impl Get<u32> for SimpleDataFeedGet {
//!     fn get() -> u32 {
//!         // it's a way to convert DataType to expected type
//!         match StorageArgument::get() {
//!             pallet_data_feed::DataType::U128(d) => d.saturated_into::<u32>(),
//!             _ => 0, // return a default value
//!         }
//!     }
//! }
//! impl template::Trait for Runtime {
//!     type Event = Event;
//!     type Data = SimpleDataFeedGet;
//! }
//! // in data-feed module
//! // 1. first need to register DataProvider.
//! // 2. then need to register StorageKey:
//! //      1. use extrinsic to call `register_storage_key`
//! //      2. the param: `key: StorageKey` is a bytes from template module using `:StorageArgument:`
//! //      (which is generated from macro `parameter_types`, if developer use other method for storage, use that storage key)
//! //      3. the param: `info: FeededDataInfo<T::BlockNumber>` would contain operation type, schedule block interval and so no.
//! // 3. use offchain worker or a program beside the chain to submit `feed_data` extrinsic to feed data.
//! // 4. template module could use T::Data::get() to use the feeded data.
//! ```
//!
//! And this module implemented the offchain, which could submit extrinsic to feed data for a existed key.
//! If a data for a key need to submit from offchain, should do following thing:
//! 1. implement `AuthorityId` for current pallet `trait`
//! 	refer to example in `example-offchain-worker`, developer could implement like this in runtime/lib.rs
//! 	```nocompile
//!		pub struct DataFeedId;
//! 	impl frame_system::offchain::AppCrypto<<Signature as sp_runtime::traits::Verify>::Signer, Signature> for DataFeedId {
//! 		type RuntimeAppPublic = pallet_data_feed::crypto::AuthorityId;
//! 		type GenericSignature = sp_core::sr25519::Signature;
//! 		type GenericPublic = sp_core::sr25519::Public;
//! 	}
//! 	impl pallet_data_feed::Trait for Runtime {
//! 		type Event = Event;
//! 		type AuthorityId = DataFeedId;
//! 		type DispatchOrigin = frame_system::EnsureSignedBy<DataFeed, AccountId>;
//! 		type WeightInfo = ();
//! 	}
//! 	```
//! 2. after register a `StorageKey`, user should set a url for this `StorageKey`
//! 	```nocompile
//! 	// submit a extrinsic to call `Call::set_url(...)`
//! 	```
//! 3. after set url for a key, user need to set offchain period for this `StorageKey`
//! 	note, if pass `None` for `period` parameter, would remove the period for this `StorageKey`.
//! 	and if the period not existed for a `StorageKey`(OffchainPeriod::get(key).is_none()),
//! 	the offchain would not work for this `StorageKey`.
//! 	```nocompile
//! 	// submit a extrinsic to call `Call::set_offchain_period(...)`
//! 	```
//! 4. after register provider, the provider could add his private key into node through rpc
//! 	`author_insertKey`, the identity is the string value of `crate::KEY_TYPE`
//! 5. then, the offchain could auto work.
//!
//! ## Genesis config
//!
//! ## Assumptions
//!

#![cfg_attr(not(feature = "std"), no_std)]

mod benchmarking;
mod default_weight;
#[cfg(test)]
mod tests;

use codec::{Decode, Encode};
use lite_json::json::{JsonValue, NumberValue};

use sp_core::crypto::KeyTypeId;
use sp_runtime::{
	offchain::{http, storage::StorageValueRef, Duration},
	traits::{CheckedAdd, CheckedDiv, StaticLookup, Zero},
	DispatchError, DispatchResult, FixedPointNumber, FixedU128, RuntimeDebug,
};
use sp_std::{prelude::*, str::Chars};

use frame_support::{
	debug, decl_error, decl_event, decl_module, decl_storage, ensure,
	traits::{Contains, EnsureOrigin},
	weights::Weight,
	IterableStorageDoubleMap, IterableStorageMap,
};
use frame_system::{
	ensure_signed,
	offchain::{AppCrypto, CreateSignedTransaction, SendSignedTransaction, Signer},
};

/// The identifier for data-feed-specific crypto keys
pub const KEY_TYPE: KeyTypeId = KeyTypeId(*b"dafe");
pub const RING_BUF_LEN: usize = 8;
pub const MAX_KEY_LEN: usize = 8;
pub const MAX_PROVIDER_LEN: usize = 8;
pub type StorageKey = Vec<u8>;

pub mod crypto {
	use super::KEY_TYPE;
	use sp_core::sr25519::Signature as Sr25519Signature;
	use sp_runtime::{
		app_crypto::{app_crypto, sr25519},
		traits::Verify,
	};
	app_crypto!(sr25519, KEY_TYPE);

	pub type AuthoritySignature = Signature;
	pub type AuthorityId = Public;

	pub struct Sr25519DataFeedAuthId;
	impl frame_system::offchain::AppCrypto<<Sr25519Signature as Verify>::Signer, Sr25519Signature>
		for Sr25519DataFeedAuthId
	{
		type RuntimeAppPublic = AuthorityId;
		type GenericSignature = sp_core::sr25519::Signature;
		type GenericPublic = sp_core::sr25519::Public;
	}
}

/// The operation type that specifies how we calculate the data
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Encode, Decode, RuntimeDebug)]
pub enum Operations {
	Average,
	Sum,
}

/// A "generic" numeric data type, which can be used in other pallets
/// as a storage value. `lite_json:json::NumberValue` can be converted into
/// DataType with helper functions.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Encode, Decode, RuntimeDebug)]
pub enum DataType {
	U128(u128),
	FixedU128(FixedU128),
}

impl From<u128> for DataType {
	fn from(n: u128) -> Self {
		DataType::U128(n)
	}
}

impl From<FixedU128> for DataType {
	fn from(f: FixedU128) -> Self {
		DataType::FixedU128(f)
	}
}

impl DataType {
	pub fn number_type(&self) -> NumberType {
		match self {
			DataType::U128(_) => NumberType::U128,
			DataType::FixedU128(_) => NumberType::FixedU128,
		}
	}

	pub fn into_fixed_u128(self) -> Option<FixedU128> {
		match self {
			DataType::FixedU128(f) => Some(f),
			_ => None,
		}
	}

	pub fn from_number_value(val: NumberValue, target_type: NumberType) -> Option<Self> {
		match target_type {
			NumberType::U128 => {
				if val.integer < 0 {
					return None;
				}
				Some(DataType::U128(val.integer as u128))
			}
			NumberType::FixedU128 => {
				if val.integer < 0 {
					return None;
				}
				let decimal_point = -(val.fraction_length as i32) + val.exponent;
				let (n, d) = if decimal_point >= 0 {
					// e.g. 1.35 * 10^3
					// integer part is (1 * 10^2 + 35) * 10^(-2+3)
					// decimal part is 1
					let n = (val.integer * 10_i64.pow(val.fraction_length) + val.fraction as i64)
						* 10_i64.pow(decimal_point as u32);
					let d = 1;
					(n, d)
				} else {
					// e.g. 1.35 * 10^-2
					// integer part is (1 * 10^2 + 35)
					// decimal part is 10^(|-2-2|)
					let n = val.integer * 10_i64.pow(val.fraction_length) + val.fraction as i64;
					// let d = decimal_point.abs();
					let d = 10_i64.pow(decimal_point.abs() as u32);
					(n, d)
				};
				let res = FixedU128::from((n, d));
				Some(DataType::FixedU128(res))
			}
		}
	}
}
impl Default for DataType {
	fn default() -> Self {
		DataType::U128(0)
	}
}

/// Types of DataType
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Encode, Decode, RuntimeDebug)]
pub enum NumberType {
	U128,
	FixedU128,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Encode, Decode, RuntimeDebug)]
pub struct FeededDataInfo<BlockNumber> {
	/// the key of what we want from the json callback
	key_str: Vec<u8>,
	number_type: NumberType,
	operation: Operations,
	schedule: BlockNumber,
}

impl<BlockNumber> FeededDataInfo<BlockNumber> {
	fn key_str(&self) -> &[u8] {
		&self.key_str
	}

	fn number_type(&self) -> NumberType {
		self.number_type
	}
}

pub trait WeightInfo {
	fn register_storage_key() -> Weight;
	fn remove_storage_key() -> Weight;
	fn set_url() -> Weight;
	fn set_offchain_period() -> Weight;
	fn feed_data() -> Weight;
	fn add_provider() -> Weight;
	fn remove_provider() -> Weight;
}

pub trait Trait: CreateSignedTransaction<Call<Self>> {
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
	/// The identifier type for an offchain worker.
	type AuthorityId: AppCrypto<Self::Public, Self::Signature>;
	/// The origin that can control `StorageKey`, control `ActiveProviders` and other key information
	type DataFeedOrigin: EnsureOrigin<Self::Origin>;
	/// WeightInfo
	type WeightInfo: WeightInfo;
}

decl_event!(
	pub enum Event<T>
	where
		AccountId = <T as frame_system::Trait>::AccountId,
		BlockNumber = <T as frame_system::Trait>::BlockNumber,
	{
		/// Register a storage key
		RegisterStorageKey(StorageKey),
		/// Remove a storage key
		RemoveStorageKey(StorageKey),
		/// Add a provider accountid
		AddProvider(AccountId),
		/// Remove a provider accountid
		RemoveProvider(AccountId),
		/// Set url for a key, which would be used in offchain
		SetUrl(StorageKey, Vec<u8>),
		/// New data stored on blockchain
		FeedData(AccountId, StorageKey, DataType),
		/// Set calculated data
		SetData(StorageKey, Option<DataType>),
		/// Set offchain
		SetOffchainPeriod(StorageKey, Option<BlockNumber>),
	}
);

// Errors inform users that something went wrong.
decl_error! {
	pub enum Error for Module<T: Trait> {
		/// If the storage key already registered
		ExistingKey,
		/// You can not put data under the key that is not registered
		InvalidKey,
		/// If the data type does not match the one specified in DataInfo
		InvalidValue,
		/// User is not allowed to feed data onto the blockchain
		NotAllowed,
		/// Provider count of key count exceed limit
		ExceededLimit,
		/// Not allow to use offchain to submit.
		NotAllowOffchain,
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as DataFeed {
		/// A set of storage keys
		/// A storage key in this set refers to a storage value in other pallets,
		pub ActiveParamTypes get(fn all_keys): Vec<StorageKey>;

		/// A set of accounts
		/// Any one can submit data on chain, while only the data submitted by
		/// the provider in this set is valid, and will be calculated later.
		pub ActiveProviders get(fn all_providers): Vec<T::AccountId>;

		/// Data Attributes.
		/// It defines the type of the data, how to extract the data we want
		/// from a json blob
		pub DataInfo get(fn data_info): map hasher(twox_64_concat) StorageKey => Option<FeededDataInfo<T::BlockNumber>>;

		/// Permissible URL that could be used to fetch data
		pub Url get(fn url): map hasher(twox_64_concat) StorageKey => Option<Vec<u8>>;

		/// Feeded Data stored in a ring buffer, which MUST ALWAYS be full of valid values.
		/// when receive new data, if would drop last old data and receive new one in front of buffer.
		pub DataFeeds get(fn feeded_data):
			double_map hasher(twox_64_concat) StorageKey, hasher(blake2_128_concat) T::AccountId => Option<[DataType; RING_BUF_LEN]>;

		/// Scheduled interval height for submitting data from a offchain call. If not set this,
		/// the offchain call would not auto work.
		pub OffchainPeriod get(fn offchain_period):
			map hasher(twox_64_concat) StorageKey => Option<T::BlockNumber>;
	}
}

impl<T: Trait> Contains<T::AccountId> for Module<T> {
	fn sorted_members() -> Vec<T::AccountId> {
		Self::all_providers()
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;
		fn deposit_event() = default;

		/// Register a storage key under which the value can be modified
		/// by this data feed pallet with some rules
		#[weight = T::WeightInfo::register_storage_key()]
		pub fn register_storage_key(origin, key: StorageKey, info: FeededDataInfo<T::BlockNumber>) -> DispatchResult {
			T::DataFeedOrigin::ensure_origin(origin)?;
			// parse origin
			ActiveParamTypes::try_mutate::<_, DispatchError, _>(|v| {
				if v.contains(&key) {
					Err(Error::<T>::ExistingKey)?;
				}
				if v.len() + 1 > MAX_KEY_LEN {
					Err(Error::<T>::ExceededLimit)?
				}

				v.push(key.clone());
				Ok(())
			})?;
			DataInfo::<T>::insert(&key, info);
			Self::deposit_event(RawEvent::RegisterStorageKey(key));
			Ok(())
		}

		/// remove the storage key from the limited set so the data feed pallet no longer
		/// can change the corresponding value afterwards.
		#[weight = T::WeightInfo::remove_storage_key()]
		pub fn remove_storage_key(origin, key: StorageKey) -> DispatchResult {
			T::DataFeedOrigin::ensure_origin(origin)?;
			ActiveParamTypes::mutate(|v| {
				// remove key
				v.retain(|k| k != &key);
			});
			DataInfo::<T>::remove(&key);
			Url::remove(&key);
			DataFeeds::<T>::remove_prefix(&key);
			Self::deposit_event(RawEvent::RemoveStorageKey(key));
			Ok(())
		}

		/// Set a url for a key which used in offchain to fetch data from this url.
		#[weight = T::WeightInfo::set_url()]
		pub fn set_url(origin, key: StorageKey, url: Vec<u8>) -> DispatchResult {
			T::DataFeedOrigin::ensure_origin(origin)?;
			let _ = Self::data_info(&key).ok_or(Error::<T>::InvalidKey)?;

			Url::insert(&key, &url);
			Self::deposit_event(RawEvent::SetUrl(key, url));
			Ok(())
		}

		/// Set a offchain period for a key, if `period` is None, would remove this period.
		/// The offchain worker can only work after the period be set, if not set a period for a key,
		/// the offchain worker would not submmit data for this key.
		#[weight = T::WeightInfo::set_offchain_period()]
		pub fn set_offchain_period(origin, key: StorageKey, period: Option<T::BlockNumber>) -> DispatchResult {
			T::DataFeedOrigin::ensure_origin(origin)?;

			match period {
				Some(p) => {
					let _ = Self::data_info(&key).ok_or(Error::<T>::InvalidKey)?;
					// if not set url, we do not allow to set period for offchain
					let _ = Self::url(&key).ok_or(Error::<T>::NotAllowOffchain)?;
					OffchainPeriod::<T>::insert(&key, p);
				},
				None => OffchainPeriod::<T>::remove(&key),
			}
			Self::deposit_event(RawEvent::SetOffchainPeriod(key, period));
			Ok(())
		}

		/// Submit a new data under the specific storage key.
		#[weight = T::WeightInfo::feed_data()]
		pub fn feed_data(origin, key: StorageKey, value: DataType) -> DispatchResult {
			// use `enusre_signed` rather than `T::DataFeedOrigin::ensure_origin`
			// for `T::DataFeedOrigin` may not same as `ActiveProviders`
			let who = ensure_signed(origin)?;
			// make sure the caller is a provider
			ensure!(Self::all_providers().contains(&who), Error::<T>::NotAllowed);

			Self::feed_data_impl(who, key, value)
		}

		/// Add a provider to current provider collection.
		#[weight = T::WeightInfo::add_provider()]
		pub fn add_provider(origin, new_one: <T::Lookup as StaticLookup>::Source) -> DispatchResult {
			T::DataFeedOrigin::ensure_origin(origin)?;
			let new_one = T::Lookup::lookup(new_one)?;

			ActiveProviders::<T>::try_mutate(|v| -> DispatchResult {
				if !v.contains(&new_one) {
					if v.len() + 1 > MAX_KEY_LEN {
						Err(Error::<T>::ExceededLimit)?
					}

					v.push(new_one.clone());
				}
				Ok(())
			})?;
			Self::deposit_event(RawEvent::AddProvider(new_one));
			Ok(())
		}

		/// Remove a provider from current provider collection.
		#[weight = T::WeightInfo::remove_provider()]
		pub fn remove_provider(origin, who: <T::Lookup as StaticLookup>::Source) -> DispatchResult {
			T::DataFeedOrigin::ensure_origin(origin)?;
			let who = T::Lookup::lookup(who)?;

			ActiveProviders::<T>::mutate(|v| {
				v.retain(|accountid| accountid != &who);
			});
			Self::deposit_event(RawEvent::RemoveProvider(who));
			Ok(())
		}

		fn on_finalize(n: T::BlockNumber) {
			for (key, info) in DataInfo::<T>::iter() {
				if  n % info.schedule == Zero::zero() {
					Self::calc(key, info);
				}
			}
		}

		fn offchain_worker(block_number: T::BlockNumber) {
			debug::native::info!("Initialize offchain workers!");

			for key in Self::all_keys() {
				if let Some(period) = Self::offchain_period(&key) {
					if Self::check_period(&key, block_number, period) {
						let res = Self::fetch_and_send_signed(&key);
						if let Err(e) = res {
							debug::error!("Error: {}", e);
						}
					}
				}
			}
		}
	}
}

impl<T: Trait> Module<T> {
	fn feed_data_impl(who: T::AccountId, key: StorageKey, value: DataType) -> DispatchResult {
		if !Self::all_keys().contains(&key) {
			Err(Error::<T>::InvalidKey)?
		}
		let info: FeededDataInfo<_> = Self::data_info(&key).ok_or(Error::<T>::InvalidKey)?;
		if value.number_type() != info.number_type {
			Err(Error::<T>::InvalidValue)?
		}
		debug::info!("Feeding data to {:?}", key);
		DataFeeds::<T>::try_mutate_exists(key.clone(), who.clone(), |data| {
			match data {
				Some(data) => {
					let mut new_data = [Default::default(); RING_BUF_LEN];
					new_data[0] = value;
					// move data buf to new_data buf, and drop last item
					new_data[1..].copy_from_slice(&data[0..(data.len() - 2)]);
					*data = new_data;
				}
				None => {
					*data = Some([value; RING_BUF_LEN]);
				}
			}
			Self::deposit_event(RawEvent::FeedData(who, key, value));
			Ok(())
		})
	}

	fn calc_impl<N: CheckedAdd + CheckedDiv + Copy, F: FnOnce(usize) -> N>(
		numbers: &[N],
		zero: N,
		convert: F,
		op: Operations,
	) -> Option<N> {
		let sum_func = |numbers: &[N]| -> Option<N> {
			let mut sum = zero;
			for n in numbers.iter() {
				sum = match sum.checked_add(n) {
					Some(n) => n,
					None => return None,
				};
			}
			Some(sum)
		};

		match op {
			Operations::Sum => sum_func(numbers),
			Operations::Average => {
				if numbers.is_empty() {
					None
				} else {
					let sum = sum_func(numbers)?;
					let n = convert(numbers.len());
					sum.checked_div(&n)
				}
			}
		}
	}

	fn calc(key: StorageKey, info: FeededDataInfo<T::BlockNumber>) {
		// calc result would drain all old data
		let data: Vec<DataType> =
			DataFeeds::<T>::drain_prefix(&key).fold(Vec::new(), |mut src, (who, datas)| {
				// filter if account not in providers now
				if Self::all_providers().contains(&who) {
					src.extend(&datas);
				}
				src
			});
		if data.is_empty() {
			debug::warn!(
				"do not receive data feed from outside for this key: {:?}",
				key
			);
			return;
		}

		let result = match info.number_type {
			NumberType::U128 => {
				let numbers = data
					.into_iter()
					.filter_map(|num: DataType| match num {
						DataType::U128(a) => Some(a),
						DataType::FixedU128(_) => None,
					})
					.collect::<Vec<u128>>();

				let res: Option<u128> =
					Self::calc_impl(&numbers, 0_u128, |len| len as u128, info.operation);
				res.map(DataType::U128)
			}
			NumberType::FixedU128 => {
				let numbers = data
					.into_iter()
					.filter_map(|num: DataType| match num {
						DataType::U128(_) => None,
						DataType::FixedU128(a) => Some(a),
					})
					.collect::<Vec<FixedU128>>();

				let res = Self::calc_impl(
					&numbers,
					FixedU128::zero(),
					|len| FixedU128::from(len as u128),
					info.operation,
				);
				res.map(DataType::FixedU128)
			}
		};

		Self::set_storage_value(key, result);
	}

	fn set_storage_value(key: StorageKey, value: Option<DataType>) {
		use frame_support::storage::unhashed;
		match value {
			Some(v) => unhashed::put(&key, &v),
			None => unhashed::kill(&key),
		}
		Self::deposit_event(RawEvent::SetData(key, value));
	}
}

// offchain
impl<T: Trait> Module<T> {
	fn check_period(
		storage_key: &StorageKey,
		block_number: T::BlockNumber,
		period: T::BlockNumber,
	) -> bool {
		let mut ref_key = b"data_feed::period:".to_vec();
		ref_key.extend_from_slice(&storage_key);
		let val = StorageValueRef::persistent(&ref_key);

		const RECENTLY_SENT: () = ();
		match val.mutate(
			|last_send: Option<Option<T::BlockNumber>>| match last_send {
				Some(Some(block)) if block_number < block + period => Err(RECENTLY_SENT),
				_ => Ok(block_number),
			},
		) {
			// in the period or failed to write the block number (acquire a lock)
			Err(RECENTLY_SENT) | Ok(Err(_)) => false,
			Ok(Ok(_)) => true,
		}
	}

	fn fetch_and_send_signed(storage_key: &StorageKey) -> Result<(), &'static str> {
		// TODO need offchain to provide a method to filter accountid
		// (`with_filter` just allow `Public` not `AccountId`, and on the other hand,
		// there is no way to get all keys to handle them),
		// currently could not do it, just peek one key to sign and submit
		let signer = Signer::<T, T::AuthorityId>::any_account();
		if !signer.can_sign() {
			return Err(
				"No local accounts available. Consider adding one via `author_insertKey` RPC.",
			)?;
		}

		let data = Self::fetch_data(storage_key)?;

		let results =
			signer.send_signed_transaction(|_account| Call::feed_data(storage_key.to_vec(), data));

		for (acc, res) in &results {
			match res {
				Ok(()) => debug::info!("[{:?}] Submitted data: {:?}", acc.id, data),
				Err(e) => debug::error!("[{:?}] Failed to submit transaction: {:?}", acc.id, e),
			}
		}

		Ok(())
	}

	fn fetch_data(storage_key: &StorageKey) -> Result<DataType, &'static str> {
		// We want to keep the offchain worker execution time reasonable, so we set a hard-coded
		// deadline to 2s to complete the external call.
		// You can also wait idefinitely for the response, however you may still get a timeout
		// coming from the host machine.
		let deadline = sp_io::offchain::timestamp().add(Duration::from_millis(2_000));
		let url = Self::url(storage_key).ok_or("no url for this storage key")?;

		let request =
			http::Request::get(core::str::from_utf8(&url).map_err(|_| "parse url error")?);

		// to alter request headers or stream body content in case of non-GET requests.
		let pending = request
			.deadline(deadline)
			.send()
			.map_err(|_| "Request had timed out.")?;

		let response = pending
			.try_wait(deadline)
			.map_err(|_| "Deadline has been reached")?
			.map_err(|_| "http error")?;
		// Let's check the status code before we proceed to reading the response.
		if response.code != 200 {
			debug::warn!("Unexpected status code: {}", response.code);
			Err("Unknown error has been encountered.")?;
		}

		let body = response.body().collect::<Vec<u8>>();
		let info = Self::data_info(&storage_key).ok_or("storage key not exist")?;
		let number_type = info.number_type();

		// Create a str slice from the body.
		let body_str = sp_std::str::from_utf8(&body).map_err(|_| {
			debug::warn!("No UTF8 body");
			"Unknown error has been encountered."
		})?;
		let key_str = core::str::from_utf8(info.key_str())
			.map_err(|_| "json key is invalid")?
			.chars();
		let data = match Self::parse_data(key_str, number_type, body_str) {
			Some(data) => Ok(data),
			None => {
				debug::warn!("Unable to extract price from the response: {:?}", body_str);
				Err("Unknown error has been encountered.")
			}
		}?;
		Ok(data)
	}

	fn parse_data(key_str: Chars, number_type: NumberType, data: &str) -> Option<DataType> {
		let mut key_str = key_str;
		let val = lite_json::parse_json(data);
		let output = val.ok().and_then(|v| match v {
			JsonValue::Object(obj) => obj
				.into_iter()
				.find(|(k, _)| k.iter().all(|k| Some(*k) == key_str.next()))
				.and_then(|v| match v.1 {
					JsonValue::Number(number) => Some(number),
					_ => None,
				}),
			_ => None,
		})?;

		DataType::from_number_value(output, number_type)
	}
}
