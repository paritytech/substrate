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
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! # Offchain Worker Example Module
//!
//! The Offchain Worker Example: A simple example of a runtime module demonstrating
//! concepts, APIs and structures common to most offchain workers.
//!
//! Run `cargo doc --package pallet-example-offchain-worker --open` to view this module's documentation.
//!
//! - \[`pallet_example_offchain_worker::Trait`](./trait.Trait.html)
//! - \[`Call`](./enum.Call.html)
//! - \[`Module`](./struct.Module.html)
//!
#![warn(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::{
	debug,
	dispatch::DispatchResult, decl_module, decl_storage, decl_event,
	weights::SimpleDispatchInfo,
};
use frame_system::{self as system, ensure_signed, ensure_none, offchain};
use serde_json as json;
use sp_core::crypto::KeyTypeId;
use sp_runtime::{
	offchain::{http, Duration},
	traits::{Zero, UniqueSaturatedFrom},
	transaction_validity::{InvalidTransaction, ValidTransaction, TransactionValidity},
};

#[cfg(test)]
mod tests;

/// Defines application identifier for crypto keys of this module.
///
/// Every module that deals with signatures needs to declare it's unique identifier for
/// it's crypto keys.
/// When offchain worker is signing transactions it's going to request keys with below
/// `KeyTypeId` from the keystore and use the ones it founds to sign the transaction.
/// The keys can be inserted manually via RPC (see `author_insertKey`).
pub const KEY_TYPE: KeyTypeId = KeyTypeId(*b"btc!");

/// Based on the above `KeyTypeId` we need to generate a pallet-specific crypto type wrappers.
/// We can use from supported crypto kinds (`sr25519`, `ed25519` and `ecdsa`) and augment
/// the types with this pallet-specific identifier.
pub mod crypto {
	use super::KEY_TYPE;
	use sp_runtime::app_crypto::{app_crypto, sr25519};
	app_crypto!(sr25519, KEY_TYPE);
}

/// A base trait for this pallet.
pub trait Trait: frame_system::Trait {
	/// The type to sign and submit transactions.
	type SubmitSignedTransaction:
		offchain::SubmitSignedTransaction<Self, <Self as Trait>::Call>;
	/// The type to submit unsigned transactions.
	type SubmitUnsignedTransaction:
		offchain::SubmitUnsignedTransaction<Self, <Self as Trait>::Call>;

	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
	/// The overarching event type.
	type Call: From<Call<Self>>;
}

/// Number of blocks of cooldown after unsigned transaction is included.
///
/// This ensure that we only accept unsigned transaction once, every `UNSIGNED_INTERVAL` blocks.
const UNSIGNED_INTERVAL: u128 = 128;

decl_storage! {
	trait Store for Module<T: Trait> as Example {
		/// A vector of recently submitted prices.
		///
		/// This is used to calculate average price, should have bounded size.
		Prices get(fn prices): Vec<u32>;
		/// Defines the block when next unsigned transaction will be accepted.
		///
		/// To prevent spam of unsigned (and unpayed!) transactions on the network,
		/// we only allow one transaction every UNSIGNED_INTERVAL blocks.
		/// This storage entry defines when new transaction is going to be accepted.
		NextUnsignedAt get(fn next_unsigned_at): T::BlockNumber;
	}
}

decl_event!(
	/// Events generated by the module.
	pub enum Event<T> where AccountId = <T as frame_system::Trait>::AccountId {
		/// Event generated when new price is accepted to contirbute to the average.
		NewPrice(u32, AccountId),
	}
);

decl_module! {
	/// A public part of the pallet.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event() = default;

		/// Submit new price to the list.
		///
		/// This method is a public function of the module and can be called from within
		/// a transaction. It appends given `price` to current list of prices.
		///	In our example the `offchain worker` will create, sign & submit a transaction that
		///	calls this function passing the price.
		///
		/// The transaction needs to be signed (see `ensure_signed`) check, so that the caller
		/// pays fee to execute it.
		/// This makes sure that it's not easy (or rather cheap) to attack the chain by submitting
		/// excesive transactions, but note that it doesn't ensure the price oracle is actually
		/// working and receives (and provides) meaningful data.
		/// This example is not focused on correctness of the oracle itself, but rather it's
		/// purpose is to showcase offchain worker capabilities.
		#[weight = SimpleDispatchInfo::FixedNormal(10_000)]
		pub fn submit_price(origin, price: u32) -> DispatchResult {
			// Retrieve sender of the transaction.
			let who = ensure_signed(origin)?;
			// Add the price to the on-chain list.
			Self::add_price(who, price);
			Ok(())
		}

		/// Submit new price to the list via unsigned transaction.
		///
		/// Works exactly like the `submit_price` function, but since we allow sending the
		/// transaction without a signature, and hence without paying any fees,
		/// we need a way to make sure that only some transactions are accepted.
		/// This function can be called only once every `UNSIGNED_INTERVAL` blocks.
		/// Transactions that call that function are de-duplicated on the pool level
		/// via `validate_unsigned` implementation and also are rendered invalid if
		/// the function has already been called in current "session".
		///
		/// This example is not focused on correctness of the oracle itself, but rather it's
		/// purpose is to showcase offchain worker capabilities.
		pub fn submit_price_unsigned(origin, _block_number: T::BlockNumber, price: u32) -> DispatchResult {
			// This ensure that the function can only be called via unsigned transaction.
			ensure_none(origin)?;
			// Add the price to the on-chain list, but mark it as coming from an empty address.
			Self::add_price(Default::default(), price);
			// now increment the block number at which we expect next unsigned transaction.
			let current_block = <system::Module<T>>::block_number();
			<NextUnsignedAt<T>>::put(
				current_block + T::BlockNumber::unique_saturated_from(UNSIGNED_INTERVAL)
			);
			Ok(())
		}

		/// Offchain Worker entry point.
		///
		/// By implementing `fn offchain_worker` within `decl_module` you declare a new offchain
		/// worker.
		/// This function will be called when the node is fully synced and a new best block is
		/// succesfuly imported.
		/// Note that it's not guaranteed for offchain workers to run on EVERY block, there might
		/// be cases where some blocks are skipped, or for some the worker runs twice (re-orgs),
		/// so the code should be able to handle that.
		/// You can use `Local Storage` API to coordinate runs of the worker.
		fn offchain_worker(block_number: T::BlockNumber) {
			// It's a good idea to add logs to your offchain workers.
			// Using the `frame_support::debug` module you have access to
			// the same API exposed by the `log` crate.
			// Note that having logs compiled to WASM may cause the size of the
			// blob to increase significantly. You can use `RuntimeDebug` custom
			// derive to hide details of the types in WASM or use `debug::native`
			// namespace to produce logs only when the worker is running natively.
			debug::native::info!("Hello World from offchain workers!");

			// Since off-chain workers are just part of the runtime code,
			// they have direct access to the storage and other included pallets.
			//
			// We can easily import `frame_system` and retrieve a block hash
			// of the parent block.
			let block_hash = <system::Module<T>>::block_hash(block_number - 1.into());
			debug::debug!("Current block is: {:?} ({:?})", block_number, block_hash);

			// It's a good practice to keep `fn offchain_worker()` function minimal,
			// and move most of the code to separate `impl` block.
			// Here we call a helper function to calculate current average price.
			// This function reads storage entries of the current state.
			let average: Option<u32> = Self::average_price();
			debug::debug!("Current price is: {:?}", average);

			// For this example we are going to send both
			// signed and unsigned transactions depending on the block number.
			// Usually it's enough to choose either options.
			let send_signed = block_number % 2.into() == Zero::zero();
			let res = if send_signed {
				Self::fetch_price_and_send_signed()
			} else {
				Self::fetch_price_and_send_unsigned(block_number)
			};
			if let Err(e) = res {
				debug::error!("Error: {}", e);
			}
		}
	}
}

/// Most of the functions are moved outside of the `decl_module` macro.
///
/// This greately helps with error messsages, as the ones inside the macro
/// can sometimes be hard to debug.
impl<T: Trait> Module<T> {
	/// A helper function to fetch the price and send signed transaction.
	fn fetch_price_and_send_signed() -> Result<(), String> {
		use system::offchain::SubmitSignedTransaction;
		// Firstly we check if there are any accounts in the local keystore
		// that are capable of signing the transaction.
		// If not it doesn't even make sense to make external HTTP requests, since
		// we won't be able to put the results back on-chain.
		if !T::SubmitSignedTransaction::can_sign() {
			return Err(
				"No local accounts available. Consider adding one via `author_insertKey` RPC."
			)?
		}

		// Make an external HTTP request to fetch the current price.
		// Note this call will block until response is received.
		let price = Self::fetch_price().map_err(|e| format!("{:?}", e))?;

		// Received price is wrapped into a call to `submit_price` public function
		// of this module. This means that the transaction, when executed,
		// will simply call that function passing `price` as an argument.
		let call = Call::submit_price(price);

		// Using `SubmitSignedTransaction` associated type we create and submit
		// a transaction representing the call, we've just created.
		// Submit signed will return a vector of results for all
		// accounts that were found in the local keystore with expected `KEY_TYPE`.
		let results = T::SubmitSignedTransaction::submit_signed(call);
		for (acc, res) in &results {
			match res {
				Ok(()) => debug::info!("[{:?}] Submitted price of {} cents", acc, price),
				Err(e) => debug::error!("[{:?}] Failed to submit transaction: {:?}", acc, e),
			}
		}

		Ok(())
	}

	/// A helper function to fetch the price and send unsigned transaction.
	fn fetch_price_and_send_unsigned(block_number: T::BlockNumber) -> Result<(), String> {
		use system::offchain::SubmitUnsignedTransaction;
		// Make sure we don't fetch the price if unsigned transaction is going
		// to be rejected anyway.
		let next_unsigned_at = <NextUnsignedAt<T>>::get();
		if next_unsigned_at > block_number {
			return Err(
				format!("Too early to send unsigned transaction. Next at: {:?}", next_unsigned_at)
			)?
		}

		// Make an external HTTP request to fetch the current price.
		// Note this call will block until response is received.
		let price = Self::fetch_price().map_err(|e| format!("{:?}", e))?;

		// Received price is wrapped into a call to `submit_price_unsigned` public function
		// of this module. This means that the transaction, when executed,
		// will simply call that function passing `price` as an argument.
		let call = Call::submit_price_unsigned(block_number, price);

		// Now let's create an unsigned transaction out of this call
		// and submit it to the pool.
		// By default unsigned transactions are disallowed, so we need to whitelist this case
		// by writing `UnsignedValidator`. Note that it's EXTREMELY important to carefuly
		// implement unsigned validation logic, as any mistakes can lead to opening DoS or spam
		// attack vectors. See validation logic docs for more details.
		T::SubmitUnsignedTransaction::submit_unsigned(call)
			.map_err(|()| "Unable to submit unsigned transaction.".into())

	}

	/// Fetch current price and return the result in cents.
	fn fetch_price() -> Result<u32, http::Error> {
		// We want to keep the offchain worker execution time reasonable,
		// so we set a hard-coded deadline to 2s to complete the external
		// call.
		// You can also wait idefinitely for the response, however you may still
		// get a timeout coming from the host machine.
		let deadline = sp_io::offchain::timestamp().add(Duration::from_millis(2_000));
		// Initiate an external HTTP GET request.
		// This is using high-level wrappers from `sp_runtime`, for the low-level calls that
		// you can find in `sp_io`. The API is trying to be similar to `reqwest`, but
		// since we are running in a custom WASM execution environment we can't simply
		// import the library here.
		let request = http::Request::get(
			"https://min-api.cryptocompare.com/data/price?fsym=BTC&tsyms=USD"
		);
		// We set the deadline for sending of the request, note that awaiting response can
		// have a separate deadline. Next we send the request, before that it's also possible
		// to alter request headers or stream body content in case of non-GET requests.
		let pending = request
			.deadline(deadline)
			.send()
			.map_err(|_| http::Error::IoError)?;

		// The request is already being processed by the host, we are free to do anything
		// else in the worker (we can send multiple concurrent requests too).
		// At some point however we probably want to check the response though,
		// so we can block current thread and wait for it to finish.
		// Note that since the request is being driven by the host, we don't have to wait
		// for the request to have it complete, we will just not read the response.
		let response = pending.try_wait(deadline)
			.map_err(|_| http::Error::DeadlineReached)??;
		// Let's check the status code before we proceed to reading the response.
		if response.code != 200 {
			debug::warn!("Unexpected status code: {}", response.code);
			return Err(http::Error::Unknown);
		}

		// Next we want to fully read the response body and collect it to a vector of bytes.
		// Note that the return object allows you to read the body in chunks as well
		// with a way to control the deadline.
		let body = response.body().collect::<Vec<u8>>();
		// Next we parse the response using `serde_json`. Even though it's possible to
		// use `serde_derive` and deserialize to a struct it's not recommended due to
		// blob size overhead introduced by such code. Deserializing to `json::Value`
		// is much more lightweight and should be preferred, especially if we only
		// care about a small number of properties from the response.
		let val: Result<json::Value, _> = json::from_slice(&body);
		// Let's parse the price as float value. Note that you should avoid using
		// floats in the runtime, it's fine to do that in the offchain worker,
		// but we do convert it to an integer before submitting on-chain.
		let price = val.ok().and_then(|v| v.get("USD").and_then(|v| v.as_f64()));
		let price = match price {
			Some(pricef) => Ok((pricef * 100.) as u32),
			None => {
				let s = core::str::from_utf8(&body);
				debug::warn!("Unable to extract price from the response: {:?}", s);
				Err(http::Error::Unknown)
			}
		}?;

		debug::warn!("Got price: {} cents", price);

		Ok(price)
	}

	/// Add new price to the list.
	fn add_price(who: T::AccountId, price: u32) {
		debug::info!("Adding to the average: {}", price);
		Prices::mutate(|prices| {
			const MAX_LEN: usize = 64;

			if prices.len() < MAX_LEN {
				prices.push(price);
			} else {
				prices[price as usize % MAX_LEN] = price;
			}
		});

		let average = Self::average_price()
			.expect("The average is not empty, because it was just mutated; qed");
		debug::info!("Current average price is: {}", average);
		// here we are raising the NewPrice event
		Self::deposit_event(RawEvent::NewPrice(price, who));
	}

	/// Calculate current average price.
	fn average_price() -> Option<u32> {
		let prices = Prices::get();
		if prices.is_empty() {
			None
		} else {
			Some(prices.iter().fold(0_u32, |a, b| a.saturating_add(*b)) / prices.len() as u32)
		}
	}
}

#[allow(deprecated)] // ValidateUnsigned
impl<T: Trait> frame_support::unsigned::ValidateUnsigned for Module<T> {
	type Call = Call<T>;

	/// Validate unsigned call to this module.
	///
	/// By default unsigned transactions are disallowed, but implementing the validator
	/// here we make sure that some particular calls (the ones produced by offchain worker)
	/// are being whitelisted and marked as valid.
	fn validate_unsigned(call: &Self::Call) -> TransactionValidity {
		// Firstly let's check that we call the right function.
		if let Call::submit_price_unsigned(block_number, new_price) = call {
			// Now let's check if the transaction has any chance to succeed.
			let next_unsigned_at = <NextUnsignedAt<T>>::get();
			if &next_unsigned_at > block_number {
				return InvalidTransaction::Stale.into();
			}
			// Let's make sure to reject transactions from the future.
			let current_block = <system::Module<T>>::block_number();
			if &current_block < block_number {
				return InvalidTransaction::Future.into();
			}

			// We prioritize transactions that are more far away from current average.
			//
			// Note this doesn't make much sense when building an actual oracle,
			// but this example is here mostly to show off offchain workers
			// capabilities, not about building an oracle.
			let avg_price = Self::average_price()
				.map(|price| if &price > new_price { price - new_price } else { new_price - price })
				.unwrap_or(0);

			Ok(ValidTransaction {
				// We set base priority to 2**20 to make sure it's included before any other
				// transactions in the pool. Next we tweak the priority depending on how much
				// it differs from the current average. (the more it differs the more priority it
				// has).
				priority: (1 << 20) + avg_price as u64,
				// This transaction does not require anything else to go before into the pool.
				// In theory we could require `previous_unsigned_at` transaction to go first,
				// but it's not necessary in our case.
				requires: vec![],
				// We set the `provides` tag to be the same as `next_unsigned_at`. This makes
				// sure only one transaction produced after `next_unsigned_at` will ever
				// get to the transaction pool and will end up in the block.
				// We can still have multiple transactions compete for the same "spot",
				// and the one with higher priority will replace other one in the pool.
				provides: vec![codec::Encode::encode(&(KEY_TYPE.0, next_unsigned_at))],
				// The transaction is only valid for next 5 blocks. After that it's
				// going to be revalidated by the pool.
				longevity: 5,
				// It's fine to propagate that transaction to other peers, which means
				// it can be created even by nodes that don't produce blocks.
				// Note that sometimes it's better to keep it for yourself (if you are the block
				// producer), since for instance in some schemes others may copy your solution and
				// claim a reward.
				propagate: true,
			})
		} else {
			InvalidTransaction::Call.into()
		}
	}
}

