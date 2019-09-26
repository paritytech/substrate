// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! # Bridge Module
//!
//! This will eventually have some useful documentation.
//! For now though, enjoy this cow's wisdom.
//!
//! ________________________________________
//! / You are only young once, but you can  \
//! \ stay immature indefinitely.           /
//! ----------------------------------------
//!        \   ^__^
//!         \  (oo)\_______
//!            (__)\       )\/\
//!                ||----w |
//!                ||     ||

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Decode, Encode};
use sr_primitives::{
	generic::BlockId,
	traits::{Block as BlockT, Header as HeaderT},
};
use support::{decl_error, decl_event, decl_module, decl_storage, dispatch::Result};
use system::{ensure_root, ensure_signed};

// struct Bridge {}
//
// impl Bridge {
// 	pub fn new() -> Self {}
// 	pub fn submit_claim() -> Result<(), Err> {}
// 	pub fn get_id(&self) -> u64 {}
// 	pub fn get_recently_finalized_block(&self) -> Block {}
// }

pub trait Trait: system::Trait + session::Trait {
	// The identifier type for an authority.
	// type AuthorityId: Member + Parameter + RuntimeAppPublic + Default;
}

decl_storage! {
	trait Store for Module<T: Trait> as Bridge {
		/// Get the ID of the current bridge
		pub BridgeId get(bridge_id): T::Hash;

		/// Get the ID of the current bridge
		// TODO: Figure out how to ge a Block here
		pub LastFinalizedBlock get(last_finalized_block): u64; // Block;

		/// Get latest block number included in the chain
		pub BlockNumber get(lastest_block_num): T::BlockNumber;

		// What I want to have wrt to the Block are:
		// 1. Block Number
		// 2. Block Hash
		// 3. State Root
		// Can I get these from a `Block`, or do they need to
		// be stored individually?

		/// Latest set of validators
		pub Validators get(validators): Vec<T::ValidatorId>;
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		// TODO: Figure out the proper type for these proofs
		fn new(origin, block_header: T::Header, validator_set: Vec<T::ValidatorId>, validator_set_proof: Vec<u8>, storage_proof: Vec<u8>) {
		//
		// The macro can't handle arguments like this :(
		// fn new(
		// 	origin,
		// 	block_header: T::Header,
		// 	validator_set: Vec<T::ValidatorId>,
		// 	validator_set_proof: Vec<u8>,
		// 	storage_proof: Vec<u8>,
		// ) {

			// NOTE: Should this be a root call?
			let _sender = ensure_signed(origin)?;

			Self::check_storage_proof()?;
			Self::check_validator_set_proof()?;

			// TODO: Do something better than this
			let bridge_id = <system::Module<T>>::random(b"this_is_not_a_good_source_of_randomness");
			<BridgeId<T>>::put(bridge_id);
		}

		fn submit_finalized_headers(origin) {
			let _sender = ensure_signed(origin)?;
		}
	}

}

decl_error! {
	// Error for the Bridge module
	pub enum Error {
		InvalidStorageProof,
		InvalidValidatorSetProof,
	}
}

impl<T: Trait> Module<T> {
	// fn check_storage_proof() -> Result<(), Error> {
	fn check_storage_proof() -> Result {
		// ... Do some math ...
		Ok(()) // Otherwise, Error::InvalidStorageProof
	}

	// fn check_validator_set_proof() -> Result<(), Error> {
	fn check_validator_set_proof() -> Result {
		// ... Do some math ...
		Ok(()) // Otherwise, Error::InvalidValidatorSetProof
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn should_initialize_default_bridge_module() {
		let bridge = Bridge::default();
	}

	#[test]
	fn should_initialize_bridge_module() {
		let bridge = Bridge::new(header, validator_set, v_set_proof, code_hash);
	}

	#[test]
	fn should_accept_finalized_headers() {
		let bridge = Bridge::default();
		bridge.submit_finalized_header(last_block_hash, header, ancestry_proof, grandpa_proof);
	}

	#[test]
	fn should_get_recently_finalized_block() {}

	#[test]
	fn should_do_all_the_things() {
		let bridge = Bridge::new(); // or Bridge::default();
		bridge.track_chain(); // Maybe part of init process?

		while curr_chain.has_blocks() {
			// Using Fred's spec this would be something like `submit_claim()`
			bridge.submit_finalized_headers();
		}

		bridge.close();
	}
}
