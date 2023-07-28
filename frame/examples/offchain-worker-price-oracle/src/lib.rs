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

//! # Price Oracle Offchain Worker Example Pallet
//!
//! The Price Oracle Offchain Worker Example: A simple pallet demonstrating
//! concepts, APIs and structures common to most offchain workers.
//!
//! Run `cargo doc --package pallet-example-offchain-worker-price-oracle --open`
//! to view this module's documentation.
//!
//! **This pallet serves as an example showcasing Substrate off-chain worker and
//! is not meant to be used in production.**
//!
//! ## Overview
//!
//! In this example we are going to build a very simplistic, naive and
//! definitely NOT production-ready oracle for BTC/USD price. The main goal is
//! to showcase how to use off-chain workers to fetch data from external sources
//! via HTTP and feed it back on-chain.
//!
//! The OCW will be triggered after every block, fetch the current price and
//! prepare either signed or unsigned transaction to feed the result back on
//! chain. The on-chain logic will simply aggregate the results and store last
//! `64` values to compute the average price.
//!
//! Only authorized keys are allowed to submit the price. The authorization key
//! should be rotated.
//!
//! Here's an example of how a node admin can inject some keys into the
//! keystore:
//!
//! ```bash
//! $ curl --location --request POST 'http://localhost:9944' \
//! --header 'Content-Type: application/json' \
//! --data-raw '{
//!     "jsonrpc": "2.0",
//!     "method": "author_insertKey",
//!     "params": ["btc!","bread tongue spell stadium clean grief coin rent spend total practice document","0xb6a8b4b6bf796991065035093d3265e314c3fe89e75ccb623985e57b0c2e0c30"],
//!     "id": 1
//! }'
//! ```
//!
//! Then make sure that the corresponding address
//! (`5GCCgshTQCfGkXy6kAkFDW1TZXAdsbCNZJ9Uz2c7ViBnwcVg`) has funds and is added
//! to `Authorities` in the runtime by adding it via `add_authority` extrinsic
//! (from `root`).
//!
//! More complex management models and session based key rotations should be
//! considered, but that’s outside the scope of this example.

#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::traits::Get;
use frame_system::{
	self as system,
	offchain::{AppCrypto, CreateSignedTransaction, SendSignedTransaction, Signer},
};
use lite_json::json::JsonValue;
use sp_core::crypto::KeyTypeId;
use sp_runtime::offchain::{
	http,
	storage::{MutateStorageError, StorageRetrievalError, StorageValueRef},
	Duration,
};
use sp_std::vec::Vec;

#[cfg(test)]
mod tests;

/// Defines application identifier for crypto keys of this module.
///
/// Every module that deals with signatures needs to declare its unique
/// identifier for its crypto keys.
///
/// When offchain worker is signing transactions it's going to request keys of
/// type `KeyTypeId` from the keystore and use the ones it finds to sign the
/// transaction. The keys can be inserted manually via RPC (see
/// `author_insertKey`).
pub const KEY_TYPE: KeyTypeId = KeyTypeId(*b"btc!");

/// Based on the above `KeyTypeId` we need to generate a pallet-specific crypto
/// type wrappers. We can use from supported crypto kinds (`sr25519`, `ed25519`
/// and `ecdsa`) and augment the types with this pallet-specific identifier.
pub mod crypto {
	use super::KEY_TYPE;
	use sp_core::sr25519::Signature as Sr25519Signature;
	use sp_runtime::{
		app_crypto::{app_crypto, sr25519},
		traits::Verify,
		MultiSignature, MultiSigner,
	};
	app_crypto!(sr25519, KEY_TYPE);

	pub struct TestAuthId;

	impl frame_system::offchain::AppCrypto<MultiSigner, MultiSignature> for TestAuthId {
		type RuntimeAppPublic = Public;
		type GenericSignature = sp_core::sr25519::Signature;
		type GenericPublic = sp_core::sr25519::Public;
	}

	// implemented for mock runtime in test
	impl frame_system::offchain::AppCrypto<<Sr25519Signature as Verify>::Signer, Sr25519Signature>
		for TestAuthId
	{
		type RuntimeAppPublic = Public;
		type GenericSignature = sp_core::sr25519::Signature;
		type GenericPublic = sp_core::sr25519::Public;
	}
}

pub use pallet::*;

#[frame_support::pallet(dev_mode)]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	/// This pallet's configuration trait
	#[pallet::config(with_default)]
	pub trait Config: CreateSignedTransaction<Call<Self>> + frame_system::Config {
		/// The identifier type for an offchain worker.
		#[pallet::no_default]
		type AuthorityId: AppCrypto<Self::Public, Self::Signature>;

		/// The overarching event type.
		#[pallet::no_default]
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// A grace period after we send transaction.
		///
		/// To avoid sending too many transactions, we only attempt to send one
		/// every `GRACE_PERIOD` blocks. We use Local Storage to coordinate
		/// sending between distinct runs of this offchain worker.
		#[pallet::no_default]
		#[pallet::constant]
		type GracePeriod: Get<BlockNumberFor<Self>>;

		/// Maximum number of prices.
		#[pallet::constant]
		type MaxPrices: Get<u32>;

		/// Maximum number of authorities.
		#[pallet::constant]
		type MaxAuthorities: Get<u32>;
	}

	/// Events for the pallet.
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Event generated when new price is accepted to contribute to the average.
		NewPrice { price: u32, maybe_who: Option<T::AccountId> },
		/// Event generated when a new authority is added.
		AuthorityAdded { authority: T::AccountId },
		/// Event generated when an authority is removed.
		AuthorityRemoved { authority: T::AccountId },
	}

	/// A vector of recently submitted prices.
	///
	/// This is used to calculate average price, should have bounded size.
	#[pallet::storage]
	#[pallet::getter(fn prices)]
	pub(super) type Prices<T: Config> = StorageValue<_, BoundedVec<u32, T::MaxPrices>, ValueQuery>;

	/// Authorities allowed to submit the price.
	#[pallet::storage]
	#[pallet::getter(fn authorities)]
	pub(super) type Authorities<T: Config> =
		StorageValue<_, BoundedVec<T::AccountId, T::MaxAuthorities>, ValueQuery>;

	#[pallet::error]
	pub enum Error<T> {
		NotAuthority,
		AlreadyAuthority,
		TooManyAuthorities,
	}

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		/// Offchain Worker entry point.
		///
		/// By implementing `fn offchain_worker` you declare a new offchain
		/// worker. This function will be called when the node is fully synced
		/// and a new best block is successfully imported.
		///
		/// Note that it's not guaranteed for offchain workers to run on EVERY
		/// block, there might be cases where some blocks are skipped, or for
		/// some the worker runs twice (re-orgs), so the code should be able to
		/// handle that.
		///
		/// You can use `Local Storage` API to coordinate runs of the worker.
		fn offchain_worker(block_number: BlockNumberFor<T>) {
			// Note that having logs compiled to WASM may cause the size of the
			// blob to increase significantly. You can use `RuntimeDebug` custom
			// derive to hide details of the types in WASM. The `sp-api` crate
			// also provides a feature `disable-logging` to disable all logging
			// and thus, remove any logging from the WASM.
			log::info!("Hello World from offchain workers!");

			// Since off-chain workers are just part of the runtime code, they
			// have direct access to the storage and other included pallets.
			//
			// We can easily import `frame_system` and retrieve a block hash of
			// the parent block.
			let parent_hash = <system::Pallet<T>>::block_hash(block_number - 1u32.into());
			log::debug!("Current block: {:?} (parent hash: {:?})", block_number, parent_hash);

			// It's a good practice to keep `fn offchain_worker()` function
			// minimal, and move most of the code to separate `impl` block. Here
			// we call a helper function to calculate current average price.
			// This function reads storage entries of the current state.
			let average: Option<u32> = Self::average_price();
			log::debug!("Current price: {:?}", average);

			/// A friendlier name for the error that is going to be returned in
			/// case we are in the grace period.
			const RECENTLY_SENT: () = ();

			// Start off by creating a reference to Local Storage value. Since
			// the local storage is common for all offchain workers, it's a good
			// practice to prepend your entry with the module name.
			let val = StorageValueRef::persistent(b"example_ocw::last_send");
			// The Local Storage is persisted and shared between runs of the
			// offchain workers, and offchain workers may run concurrently. We
			// can use the `mutate` function, to write a storage entry in an
			// atomic fashion. Under the hood it uses `compare_and_set`
			// low-level method of local storage API, which means that only one
			// worker will be able to "acquire a lock" and send a transaction if
			// multiple workers happen to be executed concurrently.
			let res = val.mutate(
				|last_send: Result<Option<BlockNumberFor<T>>, StorageRetrievalError>| {
					match last_send {
						// If we already have a value in storage and the block
						// number is recent enough we avoid sending another
						// transaction at this time.
						Ok(Some(block)) if block_number < block + T::GracePeriod::get() =>
							Err(RECENTLY_SENT),
						// In every other case we attempt to acquire the lock
						// and send a transaction.
						_ => Ok(block_number),
					}
				},
			);

			// The result of `mutate` call will give us a nested `Result` type.
			// The first one matches the return of the closure passed to
			// `mutate`, i.e. if we return `Err` from the closure, we get an
			// `Err` here. In case we return `Ok`, here we will have another
			// (inner) `Result` that indicates if the value has been set to the
			// storage correctly - i.e. if it wasn't written to in the meantime.
			match res {
				// The value has been set correctly, which means we can safely
				// send a transaction now.
				Ok(_) =>
					if let Err(e) = Self::fetch_price_and_send_signed() {
						log::error!("Error: {}", e);
					},
				// We are in the grace period, we should not send a transaction
				// this time.
				Err(MutateStorageError::ValueFunctionFailed(RECENTLY_SENT)) => {
					log::info!("Sent transaction too recently, waiting for grace period.")
				},
				// We wanted to send a transaction, but failed to write the
				// block number (acquire a lock). This indicates that another
				// offchain worker that was running concurrently most likely
				// executed the same logic and succeeded at writing to storage.
				// Thus we don't really want to send the transaction, knowing
				// that the other run already did.
				Err(MutateStorageError::ConcurrentModification(_)) => {
					log::error!("OCW failed to acquire a lock.")
				},
			}
		}
	}

	/// A public part of the pallet.
	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Submit new price to the list.
		///
		/// This method is a public function of the module and can be called
		/// from within a transaction. It appends given `price` to current list
		/// of prices. In our example the `offchain worker` will create, sign &
		/// submit a transaction that calls this function passing the price.
		///
		/// This only works if the caller is in `Authorities`.
		#[pallet::call_index(0)]
		pub fn submit_price(origin: OriginFor<T>, price: u32) -> DispatchResultWithPostInfo {
			// Retrieve sender of the transaction.
			let who = ensure_signed(origin)?;

			match Self::is_authority(&who) {
				true => Self::add_price(Some(who), price),
				false => return Err(Error::<T>::NotAuthority.into()),
			}

			// Authorized OCWs don't need to pay fees
			Ok(Pays::No.into())
		}

		#[pallet::call_index(1)]
		pub fn add_authority(
			origin: OriginFor<T>,
			authority: T::AccountId,
		) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;

			ensure!(!Self::is_authority(&authority), Error::<T>::AlreadyAuthority);

			let mut authorities = <Authorities<T>>::get();
			match authorities.try_push(authority.clone()) {
				Ok(()) => (),
				Err(_) => return Err(Error::<T>::TooManyAuthorities.into()),
			};

			Authorities::<T>::set(authorities);

			Self::deposit_event(Event::AuthorityAdded { authority });

			Ok(().into())
		}

		#[pallet::call_index(2)]
		pub fn remove_authority(
			origin: OriginFor<T>,
			authority: T::AccountId,
		) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;

			ensure!(Self::is_authority(&authority), Error::<T>::NotAuthority);

			let mut authorities = <Authorities<T>>::get();
			match authorities.iter().position(|a| a == &authority) {
				Some(index) => authorities.swap_remove(index),
				None => return Err(Error::<T>::NotAuthority.into()),
			};

			Authorities::<T>::set(authorities);

			Self::deposit_event(Event::AuthorityAdded { authority });

			Ok(().into())
		}
	}

	/// Container for different types that implement [`DefaultConfig`]` of this pallet.
	pub mod config_preludes {
		// This will help use not need to disambiguate anything when using `derive_impl`.
		use super::*;

		/// A type providing default configurations for this pallet in testing environment.
		pub struct TestDefaultConfig;

		#[frame_support::register_default_impl(TestDefaultConfig)]
		impl DefaultConfig for TestDefaultConfig {
			type MaxPrices = frame_support::traits::ConstU32<64>;
			type MaxAuthorities = frame_support::traits::ConstU32<64>;
		}
	}
}

impl<T: Config> Pallet<T> {
	fn is_authority(who: &T::AccountId) -> bool {
		<Authorities<T>>::get().contains(who)
	}

	/// A helper function to fetch the price and send signed transaction.
	fn fetch_price_and_send_signed() -> Result<(), &'static str> {
		let signer = Signer::<T, T::AuthorityId>::all_accounts();
		if !signer.can_sign() {
			return Err(
				"No local accounts available. Consider adding one via `author_insertKey` RPC.",
			)
		}
		// Make an external HTTP request to fetch the current price. Note this
		// call will block until response is received.
		let price = Self::fetch_price().map_err(|_| "Failed to fetch price")?;

		// Using `send_signed_transaction` associated type we create and submit
		// a transaction representing the call, we've just created. Submit
		// signed will return a vector of results for all accounts that were
		// found in the local keystore with expected `KEY_TYPE`.
		let results = signer.send_signed_transaction(|_account| {
			// Received price is wrapped into a call to `submit_price` public
			// function of this pallet. This means that the transaction, when
			// executed, will simply call that function passing `price` as an
			// argument.
			Call::submit_price { price }
		});

		for (acc, res) in &results {
			match res {
				Ok(()) => log::info!("[{:?}] Submitted price of {} cents", acc.id, price),
				Err(e) => log::error!("[{:?}] Failed to submit transaction: {:?}", acc.id, e),
			}
		}

		Ok(())
	}

	/// Fetch current price and return the result in cents.
	fn fetch_price() -> Result<u32, http::Error> {
		// We want to keep the offchain worker execution time reasonable, so we
		// set a hard-coded deadline to 2s to complete the external call. You
		// can also wait indefinitely for the response, however you may still
		// get a timeout coming from the host machine.
		let deadline = sp_io::offchain::timestamp().add(Duration::from_millis(2_000));
		// Initiate an external HTTP GET request. This is using high-level
		// wrappers from `sp_runtime`, for the low-level calls that you can find
		// in `sp_io`. The API is trying to be similar to `request`, but since
		// we are running in a custom WASM execution environment we can't simply
		// import the library here.
		let request =
			http::Request::get("https://min-api.cryptocompare.com/data/price?fsym=BTC&tsyms=USD");
		// We set the deadline for sending of the request, note that awaiting
		// response can have a separate deadline. Next we send the request,
		// before that it's also possible to alter request headers or stream
		// body content in case of non-GET requests.
		let pending = request.deadline(deadline).send().map_err(|_| http::Error::IoError)?;

		// The request is already being processed by the host, we are free to do
		// anything else in the worker (we can send multiple concurrent requests
		// too). At some point however we probably want to check the response
		// though, so we can block current thread and wait for it to finish.
		// Note that since the request is being driven by the host, we don't
		// have to wait for the request to have it complete, we will just not
		// read the response.
		let response = pending.try_wait(deadline).map_err(|_| http::Error::DeadlineReached)??;
		// Let's check the status code before we proceed to reading the
		// response.
		if response.code != 200 {
			log::warn!("Unexpected status code: {}", response.code);
			return Err(http::Error::Unknown)
		}

		// Next we want to fully read the response body and collect it to a
		// vector of bytes. Note that the return object allows you to read the
		// body in chunks as well with a way to control the deadline.
		let body = response.body().collect::<Vec<u8>>();

		// Create a str slice from the body.
		let body_str = sp_std::str::from_utf8(&body).map_err(|_| {
			log::warn!("No UTF8 body");
			http::Error::Unknown
		})?;

		let price = match Self::parse_price(body_str) {
			Some(price) => Ok(price),
			None => {
				log::warn!("Unable to extract price from the response: {:?}", body_str);
				Err(http::Error::Unknown)
			},
		}?;

		log::warn!("Got price: {} cents", price);

		Ok(price)
	}

	/// Parse the price from the given JSON string using `lite-json`.
	///
	/// Returns `None` when parsing failed or `Some(price in cents)` when
	/// parsing is successful.
	fn parse_price(price_str: &str) -> Option<u32> {
		let val = lite_json::parse_json(price_str);
		let price = match val.ok()? {
			JsonValue::Object(obj) => {
				let (_, v) = obj.into_iter().find(|(k, _)| k.iter().copied().eq("USD".chars()))?;
				match v {
					JsonValue::Number(number) => number,
					_ => return None,
				}
			},
			_ => return None,
		};

		let exp = price.fraction_length.saturating_sub(2);
		Some(price.integer as u32 * 100 + (price.fraction / 10_u64.pow(exp)) as u32)
	}

	/// Add new price to the list.
	fn add_price(maybe_who: Option<T::AccountId>, price: u32) {
		log::info!("Adding to the average: {}", price);
		<Prices<T>>::mutate(|prices| {
			if prices.try_push(price).is_err() {
				prices[(price % T::MaxPrices::get()) as usize] = price;
			}
		});

		let average = Self::average_price()
			.expect("The average is not empty, because it was just mutated; qed");
		log::info!("Current average price is: {}", average);
		// here we are raising the NewPrice event
		Self::deposit_event(Event::NewPrice { price, maybe_who });
	}

	/// Calculate current average price.
	fn average_price() -> Option<u32> {
		let prices = <Prices<T>>::get();
		if prices.is_empty() {
			None
		} else {
			Some(prices.iter().fold(0_u32, |a, b| a.saturating_add(*b)) / prices.len() as u32)
		}
	}
}
