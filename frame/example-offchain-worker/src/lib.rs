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
//! \## Overview
//!
//! <!-- Original author of paragraph: Various. See https://github.com/paritytech/substrate-developer-hub/issues/44 -->
//! // Short description of module purpose.
//! // Links to Traits that should be implemented.
//! // What this module is for.
//! // What functionality the module provides.
//! // When to use the module (use case examples).
//! // How it is used.
//! // Inputs it uses and the source of each input.
//! // Outputs it produces.
//!
//! <!-- Original author of paragraph: @Kianenigma in PR https://github.com/paritytech/substrate/pull/1951 -->
//! <!-- and comment https://github.com/paritytech/substrate-developer-hub/issues/44#issuecomment-471982710 -->
//!
//! \## Terminology
//!
//! // Add terminology used in the custom module. Include concepts, storage items, or actions that you think
//! // deserve to be noted to give context to the rest of the documentation or module usage. The author needs to
//! // use some judgment about what is included. We don't want a list of every storage item nor types - the user
//! // can go to the code for that. For example, "transfer fee" is obvious and should not be included, but
//! // "free balance" and "reserved balance" should be noted to give context to the module.
//! // Please do not link to outside resources. The reference docs should be the ultimate source of truth.
//!
//! <!-- Original author of heading: @Kianenigma in PR https://github.com/paritytech/substrate/pull/1951 -->
//!
//! \## Goals
//!
//! // Add goals that the custom module is designed to achieve.
//!
//! <!-- Original author of heading: @Kianenigma in PR https://github.com/paritytech/substrate/pull/1951 -->
//!
//! \### Scenarios
//!
//! <!-- Original author of paragraph: @Kianenigma. Based on PR https://github.com/paritytech/substrate/pull/1951 -->
//!
//! \#### <INSERT_SCENARIO_NAME>
//!
//! // Describe requirements prior to interacting with the custom module.
//! // Describe the process of interacting with the custom module for this scenario and public API functions used.
//!
//! \## Interface
//!
//! \### Supported Origins
//!
//! // What origins are used and supported in this module (root, signed, none)
//! // i.e. root when <code>\`ensure_root\`</code> used
//! // i.e. none when <code>\`ensure_none\`</code> used
//! // i.e. signed when <code>\`ensure_signed\`</code> used
//!
//! <code>\`inherent\`</code> <INSERT_DESCRIPTION>
//!
//! <!-- Original author of paragraph: @Kianenigma in comment -->
//! <!-- https://github.com/paritytech/substrate-developer-hub/issues/44#issuecomment-471982710 -->
//!
//! \### Types
//!
//! // Type aliases. Include any associated types and where the user would typically define them.
//!
//! <code>\`ExampleType\`</code> <INSERT_DESCRIPTION>
//!
//! <!-- Original author of paragraph: ??? -->
//!
//! // Reference documentation of aspects such as `storageItems` and `dispatchable` functions should only be
//! // included in the https://docs.rs Rustdocs for Substrate and not repeated in the README file.
//!
//! \### Dispatchable Functions
//!
//! <!-- Original author of paragraph: @AmarRSingh & @joepetrowski -->
//!
//! // A brief description of dispatchable functions and a link to the rustdoc with their actual documentation.
//!
//! // <b>MUST</b> have link to Call enum
//! // <b>MUST</b> have origin information included in function doc
//! // <b>CAN</b> have more info up to the user
//!
//! \### Public Functions
//!
//! <!-- Original author of paragraph: @joepetrowski -->
//!
//! // A link to the rustdoc and any notes about usage in the module, not for specific functions.
//! // For example, in the balances module: "Note that when using the publicly exposed functions,
//! // you (the runtime developer) are responsible for implementing any necessary checks
//! // (e.g. that the sender is the signer) before calling a function that will affect storage."
//!
//! <!-- Original author of paragraph: @AmarRSingh -->
//!
//! // It is up to the writer of the respective module (with respect to how much information to provide).
//!
//! \#### Public Inspection functions - Immutable (getters)
//!
//! // Insert a subheading for each getter function signature
//!
//! \##### <code>\`example_getter_name()\`</code>
//!
//! // What it returns
//! // Why, when, and how often to call it
//! // When it could panic or error
//! // When safety issues to consider
//!
//! \#### Public Mutable functions (changing state)
//!
//! // Insert a subheading for each setter function signature
//!
//! \##### <code>\`example_setter_name(origin, parameter_name: T::ExampleType)\`</code>
//!
//! // What state it changes
//! // Why, when, and how often to call it
//! // When it could panic or error
//! // When safety issues to consider
//! // What parameter values are valid and why
//!
//! \### Storage Items
//!
//! // Explain any storage items included in this module
//!
//! \### Digest Items
//!
//! // Explain any digest items included in this module
//!
//! \### Inherent Data
//!
//! // Explain what inherent data (if any) is defined in the module and any other related types
//!
//! \### Events:
//!
//! // Insert events for this module if any
//!
//! \### Errors:
//!
//! // Explain what generates errors
//!
//! \## Usage
//!
//! // Insert 2-3 examples of usage and code snippets that show how to
//! // use <INSERT_CUSTOM_MODULE_NAME> module in a custom module.
//!
//! \### Prerequisites
//!
//! // Show how to include necessary imports for <INSERT_CUSTOM_MODULE_NAME> and derive
//! // your module configuration trait with the `INSERT_CUSTOM_MODULE_NAME` trait.
//!
//! \```rust
//! use <INSERT_CUSTOM_MODULE_NAME>;
//!
//! pub trait Trait: <INSERT_CUSTOM_MODULE_NAME>::Trait { }
//! \```
//!
//! \### Simple Code Snippet
//!
//! // Show a simple example (e.g. how to query a public getter function of <INSERT_CUSTOM_MODULE_NAME>)
//!
//! \### Example from SRML
//!
//! // Show a usage example in an actual runtime
//!
//! // See:
//! // - Substrate TCR https://github.com/parity-samples/substrate-tcr
//! // - Substrate Kitties https://shawntabrizi.github.io/substrate-collectables-workshop/#/
//!
//! \## Genesis Config
//!
//! <!-- Original author of paragraph: @joepetrowski -->
//!
//! \## Dependencies
//!
//! // Dependencies on other SRML modules and the genesis config should be mentioned,
//! // but not the Rust Standard Library.
//! // Genesis configuration modifications that may be made to incorporate this module
//! // Interaction with other modules
//!
//! <!-- Original author of heading: @AmarRSingh -->
//!
//! \## Related Modules
//!
//! // Interaction with other modules in the form of a bullet point list
//!
//! \## References
//!
//! <!-- Original author of paragraph: @joepetrowski -->
//!
//! // Links to reference material, if applicable. For example, Phragmen, W3F research, etc.
//! // that the implementation is based on.
//! </pre></p></details>

#![warn(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::{
	debug,
	dispatch::DispatchResult, decl_module, decl_storage, decl_event,
	weights::SimpleDispatchInfo,
};
use frame_system::{self as system, ensure_signed, offchain};
use sp_runtime::{
	offchain::{http, Duration},
	traits::Zero,
};
use sp_core::crypto::KeyTypeId;
use serde_json as json;

#[cfg(test)]
mod tests;

pub const KEY_TYPE: KeyTypeId = KeyTypeId(*b"btc!");

pub mod crypto {
	use super::KEY_TYPE;
	use sp_runtime::app_crypto::{app_crypto, sr25519};
	app_crypto!(sr25519, KEY_TYPE);
}

pub trait Trait: frame_system::Trait {
	type SubmitTransaction: offchain::SubmitSignedTransaction<Self, <Self as Trait>::Call>;

	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
	/// The overarching event type.
	type Call: From<Call<Self>>;
}

decl_storage! {
	trait Store for Module<T: Trait> as Example {
		Prices get(fn prices): Vec<u32>;
	}
}

decl_event!(
	pub enum Event<T> where AccountId = <T as frame_system::Trait>::AccountId {
		NewPrice(u32, AccountId),
	}
);

decl_module! {
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
			let who = ensure_signed(origin)?;

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
				Self::fetch_price_and_send_unsigned()
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
		if !T::SubmitTransaction::can_sign() {
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

		// Using `SubmitTransaction` associated type we create and submit
		// a transaction representing the call, we've just created.
		// Submit signed will return a vector of results for all
		// accounts that were found in the local keystore with expected `KEY_TYPE`.
		let results = T::SubmitTransaction::submit_signed(call);
		for (acc, res) in &results {
			match res {
				Ok(()) => debug::info!("[{:?}] Submitted price of {} cents", acc, price),
				Err(e) => debug::error!("[{:?}] Failed to submit transaction: {:?}", acc, e),
			}
		}

		Ok(())
	}

	fn fetch_price_and_send_unsigned() -> Result<(), String> {
		unimplemented!()
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
