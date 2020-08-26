// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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
//! The DataFeed module provides a way to feed data from external word to runtime.
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
//! data providers(also very limited set). Only a permitted account(listed in the
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
//!     oracle pallet.
//! * `remove_storage_key` - Remove a storage key whose value can no longer be touched by
//!    oracle pallet.
//! * `set_url` - Set a url under a specific key whose value can be querried from
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
//! ```
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
//! //      3. the param: `info: Info<T::BlockNumber>` would contain operation type, schedule block interval and so no.
//! // 3. use offchain worker or a program beside the chain to submit `feed_data` extrinsic to feed data.
//! // 4. template module could use `Something` to get data and use.
//! ```
//! 2. second way: the storage defined in runtime
//! ```
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
//! //      3. the param: `info: Info<T::BlockNumber>` would contain operation type, schedule block interval and so no.
//! // 3. use offchain worker or a program beside the chain to submit `feed_data` extrinsic to feed data.
//! // 4. template module could use T::Data::get() to use the feeded data.
//! ```
//!
//! ## Genesis config
//!
//! ## Assumptions
//!

#![cfg_attr(not(feature = "std"), no_std)]
