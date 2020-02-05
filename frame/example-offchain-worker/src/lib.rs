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
//! concepts, APIs and structures common to most runtime modules.
//!
//! Run `cargo doc --package pallet-example --open` to view this module's documentation.
//!
//! ### Documentation Guidelines:
//!
//! <!-- Original author of paragraph: Various. Based on collation of review comments to PRs addressing issues with -->
//! <!-- label 'S3-SRML' in https://github.com/paritytech/substrate-developer-hub/issues -->
//! <ul>
//!     <li>Documentation comments (i.e. <code>/// comment</code>) - should
//!         accompany module functions and be restricted to the module interface,
//!         not the internals of the module implementation. Only state inputs,
//!         outputs, and a brief description that mentions whether calling it
//!         requires root, but without repeating the source code details.
//!         Capitalise the first word of each documentation comment and end it with
//!         a full stop. See
//!         <a href="https://github.com/paritytech/substrate#72-contributing-to-documentation-for-substrate-packages"
//!         target="_blank"> Generic example of annotating source code with documentation comments</a></li>
//!     <li>Self-documenting code - Try to refactor code to be self-documenting.</li>
//!     <li>Code comments - Supplement complex code with a brief explanation, not every line of code.</li>
//!     <li>Identifiers - surround by backticks (i.e. <code>INHERENT_IDENTIFIER</code>, <code>InherentType</code>,
//!         <code>u64</code>)</li>
//!     <li>Usage scenarios - should be simple doctests. The compiler should ensure they stay valid.</li>
//!     <li>Extended tutorials - should be moved to external files and refer to.</li>
//!     <!-- Original author of paragraph: @AmarRSingh -->
//!     <li>Mandatory - include all of the sections/subsections where <b>MUST</b> is specified.</li>
//!     <li>Optional - optionally include sections/subsections where <b>CAN</b> is specified.</li>
//! </ul>
//!
//! ### Documentation Template:<br>
//!
//! Copy and paste this template from frame/example/src/lib.rs into file
//! `frame/<INSERT_CUSTOM_MODULE_NAME>/src/lib.rs` of your own custom module and complete it.
//! <details><p><pre>
//! // Add heading with custom module name
//!
//! \# <INSERT_CUSTOM_MODULE_NAME> Module
//!
//! // Add simple description
//!
//! // Include the following links that shows what trait needs to be implemented to use the module
//! // and the supported dispatchables that are documented in the Call enum.
//!
//! - \[`<INSERT_CUSTOM_MODULE_NAME>::Trait`](./trait.Trait.html)
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

use sp_std::marker::PhantomData;
use frame_support::{
	debug,
	dispatch::DispatchResult, decl_module, decl_storage, decl_event,
	weights::{SimpleDispatchInfo, DispatchInfo, DispatchClass, ClassifyDispatch, WeighData, Weight, PaysFee},
};
use frame_system::{self as system, ensure_signed, ensure_root, offchain};
use codec::{Encode, Decode};
use sp_runtime::{
	traits::{SignedExtension, Bounded, SaturatedConversion},
	transaction_validity::{
		ValidTransaction, TransactionValidityError, InvalidTransaction, TransactionValidity,
	},
	offchain::http,
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

// TODO [ToDr] docs
pub trait Trait: frame_system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
	/// The overarching event type.
	type Call: From<Call<Self>>;

	/// Transaction submitter.
	/// TODO [ToDr] Document
	type SubmitTransaction: offchain::SubmitSignedTransaction<Self, <Self as Trait>::Call>;
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

		/// This is your public interface. Be extremely careful.
		/// This is just a simple example of how to interact with the module from the external
		/// world.
		///
		/// TODO [ToDr] Document that this happens on-chain
		/// and is triggered by transaction.
		pub fn submit_price(origin, price: u32) -> DispatchResult {
			let who = ensure_signed(origin)?;

			debug::info!("Adding to the average: {}", price);
			let average = Prices::mutate(|prices| {
				const MAX_LEN: usize = 64;

				if prices.len() < MAX_LEN {
					prices.push(price);
				} else {
					prices[price as usize % MAX_LEN] = price;
				}

				// TODO Whatchout for overflows
				prices.iter().sum::<u32>() / prices.len() as u32
			});
			debug::info!("Current average price is: {}", average);
			// here we are raising the NewPrice event
			Self::deposit_event(RawEvent::NewPrice(price, who));
			Ok(())
		}

		// TODO [ToDr] Document
		fn offchain_worker(block_number: T::BlockNumber) {
			// TODO [ToDr] Document
			debug::RuntimeLogger::init();

			let average: Option<u32> = Self::average_price();
			debug::warn!("Hello World from offchain workers!");
			debug::warn!("Current price is: {:?}", average);

			// TODO [ToDr] Document
			let block_hash = <system::Module<T>>::block_hash(block_number - 1.into());
			debug::warn!("Current block is: {:?} ({:?})", block_number, block_hash);

			let price = match Self::fetch_price() {
				Ok(price) => {
					debug::warn!("Got price: {} cents", price);
					price
				},
				Err(_) => {
					debug::warn!("Error fetching price.");
					return
				}
			};

			// TODO [ToDr] do something with unsigned transaction too.
			Self::submit_price_on_chain(price);
		}
	}
}

impl<T: Trait> Module<T> {
	fn average_price() -> Option<u32> {
		let prices = Prices::get();
		if prices.is_empty() {
			None
		} else {
			Some(prices.iter().sum::<u32>() / prices.len() as u32)
		}
	}

	fn fetch_price() -> Result<u32, http::Error> {
		let pending = http::Request::get(
			"https://min-api.cryptocompare.com/data/price?fsym=BTC&tsyms=USD"
		).send().map_err(|_| http::Error::IoError)?;

		let response = pending.wait()?;
		if response.code != 200 {
			debug::warn!("Unexpected status code: {}", response.code);
			return Err(http::Error::Unknown);
		}

		let body = response.body().collect::<Vec<u8>>();
		let val: Result<json::Value, _> = json::from_slice(&body);
		let price = val.ok().and_then(|v| v.get("USD").and_then(|v| v.as_f64()));
		match price {
			Some(pricef) => {
				Ok((pricef * 100.) as u32)
			},
			None => {
				let s = core::str::from_utf8(&body);
				debug::warn!("Unable to extract price from the response: {:?}", s);
				Err(http::Error::Unknown)
			}
		}
	}

	fn submit_price_on_chain(price: u32) {
		use system::offchain::SubmitSignedTransaction;

		let call = Call::submit_price(price);
		let res = T::SubmitTransaction::submit_signed(call);

		if res.is_empty() {
			debug::error!("No local accounts found.");
		} else {
			debug::info!("Sent transactions from: {:?}", res);
		}
	}
}
