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

//! # Offchain Worker Example Pallet
//!
//! The Ping-Pong Offchain Worker Example: A simple pallet demonstrating
//! concepts, APIs and structures common to most offchain workers.
//!
//! Run `cargo doc --package pallet-example-offchain-worker-ping-pong --open` to
//! view this module's documentation.
//!
//! **This pallet serves as an example showcasing Substrate off-chain worker and
//! is not meant to be used in production.**
//!
//! ## Overview
//!
//! This is a simple example pallet to showcase how the runtime can and should
//! interact with an offchain worker asynchronously. It also showcases the
//! potential pitfalls and security considerations that come with it.
//!
//! It is based on [this example by
//! `gnunicorn`](https://gnunicorn.github.io/substrate-offchain-cb/), although
//! an updated version with a few modifications.
//!
//! The example plays simple ping-pong with off-chain workers: Once a signed
//! transaction to `ping` is submitted (by any user), a Ping request is written
//! into Storage. Each Ping request has a `nonce`, which is arbitrarily chosen
//! by the user (not necessarily unique).
//!
//! After every block, the offchain worker is triggered. If it sees a Ping
//! request in the current block, it reacts by sending a transaction to send a
//! Pong with the corresponding `nonce`. When `pong_*` extrinsics are executed,
//! they emit an `PongAck*` event so we can track with existing UIs.
//!
//! The `PongAck*` events come in two different flavors:
//! - `PongAckAuthenticated`: emitted when the call was made by an **authenticated** offchain worker
//!   (whitelisted via `Authorities` storage)
//! - `PongAckUnauthenticated`: emitted when the call was made by an **unauthenticated** offchain
//!   worker (or potentially malicious actors
//!
//! The security implications from `PongAckUnauthenticated` should be obvious:
//! not **ONLY** offchain workers can call `pong_unsigned*`. **ANYONE** can do
//! it, and they can actually use a different `nonce` from the original ping
//! (try it yourself!). If the `nonce` actually had some important meaning to
//! the state of our chain, this would be a **VULNERABILITY**.
//!
//! Also, unsigned transactions can easily become a vector for DoS attacks!
//!
//! This is meant to highlight the importance of solid security assumptions when
//! using unsigned transactions. In other words:
//!
//! ⚠️ **DO NOT USE UNSIGNED TRANSACTIONS UNLESS YOU KNOW EXACTLY WHAT YOU ARE
//! DOING!** ⚠️
//!
//! Here's an example of how a node admin can inject some keys into the
//! keystore, so that the OCW can call `pong_signed`:
//!
//! ```bash
//! $ curl --location --request POST 'http://localhost:9944' \
//! --header 'Content-Type: application/json' \
//! --data-raw '{
//!     "jsonrpc": "2.0",
//!     "method": "author_insertKey",
//!     "params": ["pong","bread tongue spell stadium clean grief coin rent spend total practice document","0xb6a8b4b6bf796991065035093d3265e314c3fe89e75ccb623985e57b0c2e0c30"],
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
//! considered, but that's outside the scope of this example.

#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Decode, Encode};
use frame_support::traits::Get;
use frame_system::{
	self as system,
	offchain::{
		AppCrypto, CreateSignedTransaction, SendSignedTransaction, SendUnsignedTransaction,
		SignedPayload, Signer, SigningTypes, SubmitTransaction,
	},
	pallet_prelude::*,
};
use sp_core::crypto::KeyTypeId;
use sp_runtime::{
	traits::Zero,
	transaction_validity::{InvalidTransaction, TransactionValidity, ValidTransaction},
	RuntimeDebug,
};

#[cfg(test)]
mod tests;

/// Defines application identifier for crypto keys of this module.
///
/// Every module that deals with signatures needs to declare its unique
/// identifier for its crypto keys. When offchain worker is signing transactions
/// it's going to request keys of type `KeyTypeId` from the keystore and use the
/// ones it finds to sign the transaction. The keys can be inserted manually via
/// RPC (see `author_insertKey`).
pub const KEY_TYPE: KeyTypeId = KeyTypeId(*b"pong");

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

	/// This pallet's configuration trait
	#[pallet::config(with_default)]
	pub trait Config: CreateSignedTransaction<Call<Self>> + frame_system::Config {
		/// The identifier type for an offchain worker.
		#[pallet::no_default]
		type AuthorityId: AppCrypto<Self::Public, Self::Signature>;

		/// The overarching event type.
		#[pallet::no_default]
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		// Configuration parameters

		/// Number of blocks of cooldown after unsigned transaction is included.
		///
		/// This ensures that we only accept unsigned transactions once, every `UnsignedInterval`
		/// blocks.
		#[pallet::no_default]
		#[pallet::constant]
		type UnsignedInterval: Get<BlockNumberFor<Self>>;

		/// A configuration for base priority of unsigned transactions.
		///
		/// This is exposed so that it can be tuned for particular runtime, when
		/// multiple pallets send unsigned transactions.
		#[pallet::constant]
		type UnsignedPriority: Get<TransactionPriority>;

		/// Maximum number of pings on the same block.
		#[pallet::constant]
		type MaxPings: Get<u32>;

		/// Maximum number of authorities.
		#[pallet::constant]
		type MaxAuthorities: Get<u32>;
	}

	#[pallet::error]
	pub enum Error<T> {
		NotAuthority,
		AlreadyAuthority,
		TooManyAuthorities,
		TooManyPings,
	}

	#[derive(Clone, Debug, Encode, Decode, PartialEq, Eq, scale_info::TypeInfo)]
	pub enum UnsignedType {
		UnsignedWithSignedPayload,
		RawUnsigned,
	}

	/// Events for the pallet.
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Event generated when new ping is received.
		Ping { nonce: u32 },
		/// Event generated when new pong_signed transaction is accepted.
		PongAckAuthenticated { nonce: u32 },
		/// Event generated when new pong_unsigned* transaction is accepted.
		PongAckUnauthenticated { nonce: u32, unsigned_type: UnsignedType },
		/// Event generated when a new authority is added.
		AuthorityAdded { authority: T::AccountId },
		/// Event generated when an authority is removed.
		AuthorityRemoved { authority: T::AccountId },
	}

	/// A struct for wrapping the ping nonce.
	#[derive(Encode, Decode, MaxEncodedLen, TypeInfo)]
	pub struct Ping(pub u32);

	/// A vector of recently submitted pings.
	#[pallet::storage]
	#[pallet::getter(fn pings)]
	pub(super) type Pings<T: Config> = StorageValue<_, BoundedVec<Ping, T::MaxPings>, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn authorities)]
	pub(super) type Authorities<T: Config> =
		StorageValue<_, BoundedVec<T::AccountId, T::MaxAuthorities>, ValueQuery>;

	/// Defines the block when next unsigned transaction will be accepted.
	///
	/// To prevent spam of unsigned (and unpaid!) transactions on the network,
	/// we only allow one transaction every `T::UnsignedInterval` blocks. This
	/// storage entry defines when new transaction is going to be accepted.
	#[pallet::storage]
	#[pallet::getter(fn next_unsigned_at)]
	pub(super) type NextUnsignedAt<T: Config> = StorageValue<_, BlockNumberFor<T>, ValueQuery>;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		/// Offchain Worker entry point.
		///
		/// By implementing `fn offchain_worker` you declare a new offchain
		/// worker. This function will be called when the node is fully synced
		/// and a new best block is successfully imported. Note that it's not
		/// guaranteed for offchain workers to run on EVERY block, there might
		/// be cases where some blocks are skipped, or for some the worker runs
		/// twice (re-orgs), so the code should be able to handle that. You can
		/// use `Local Storage` API to coordinate runs of the worker.
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

			// if `NextUnsignedAt` allows, try to send some unsigned pong
			let next_unsigned_at = <NextUnsignedAt<T>>::get();
			if next_unsigned_at <= block_number {
				// we choose which kind of unsigned pong based on block_number
				let unsigned_type = block_number % 3u32.into();
				if unsigned_type == Zero::zero() {
					if let Err(e) = Self::ocw_pong_raw_unsigned(block_number) {
						log::error!("Error: {}", e);
					}
				} else if unsigned_type == BlockNumberFor::<T>::from(1u32) {
					// node needs to be loaded with keys as the payload will be signed
					if let Err(e) = Self::ocw_pong_unsigned_for_any_account(block_number) {
						log::error!("Error: {}", e);
					}
				} else if unsigned_type == BlockNumberFor::<T>::from(2u32) {
					// node needs to be loaded with keys as the payload will be signed
					if let Err(e) = Self::ocw_pong_unsigned_for_all_accounts(block_number) {
						log::error!("Error: {}", e);
					}
				}
			}

			// try to send a pong_signed (node needs to be loaded with keys,
			// account needs to be funded)
			if let Err(e) = Self::ocw_pong_signed() {
				log::error!("Error: {}", e);
			}
		}

		/// clean Pings
		fn on_initialize(_: BlockNumberFor<T>) -> Weight {
			Pings::<T>::kill();
			Weight::zero()
		}
	}

	/// A public part of the pallet.
	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::call_index(0)]
		#[pallet::weight(0)]
		pub fn ping(origin: OriginFor<T>, nonce: u32) -> DispatchResultWithPostInfo {
			let _who = ensure_signed(origin)?;

			let mut pings = <Pings<T>>::get();
			match pings.try_push(pallet::Ping(nonce)) {
				Ok(()) => (),
				Err(_) => return Err(Error::<T>::TooManyPings.into()),
			};

			Pings::<T>::set(pings);

			Self::deposit_event(Event::Ping { nonce });

			Ok(().into())
		}

		#[pallet::call_index(1)]
		#[pallet::weight(0)]
		pub fn pong_signed(origin: OriginFor<T>, nonce: u32) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			match Self::is_authority(&who) {
				true => Self::deposit_event(Event::PongAckAuthenticated { nonce }),
				false => return Err(Error::<T>::NotAuthority.into()),
			}

			// Authorized OCWs don't need to pay fees
			Ok(Pays::No.into())
		}

		#[pallet::call_index(2)]
		#[pallet::weight(0)]
		pub fn pong_unsigned(
			origin: OriginFor<T>,
			_block_number: BlockNumberFor<T>,
			nonce: u32,
		) -> DispatchResultWithPostInfo {
			// This ensures that the function can only be called via unsigned
			// transaction.
			ensure_none(origin)?;

			// Emit the PongAckUnauthenticated event
			Self::deposit_event(Event::PongAckUnauthenticated {
				nonce,
				unsigned_type: UnsignedType::RawUnsigned,
			});

			// now increment the block number at which we expect next unsigned
			// transaction.
			let current_block = <system::Pallet<T>>::block_number();
			<NextUnsignedAt<T>>::put(current_block + T::UnsignedInterval::get());
			Ok(().into())
		}

		#[pallet::call_index(3)]
		#[pallet::weight(0)]
		pub fn pong_unsigned_with_signed_payload(
			origin: OriginFor<T>,
			pong_payload: PongPayload<T::Public, BlockNumberFor<T>>,
			_signature: T::Signature,
		) -> DispatchResultWithPostInfo {
			// This ensures that the function can only be called via unsigned
			// transaction.
			ensure_none(origin)?;

			Self::deposit_event(Event::PongAckUnauthenticated {
				nonce: pong_payload.nonce,
				unsigned_type: UnsignedType::UnsignedWithSignedPayload,
			});

			// now increment the block number at which we expect next unsigned
			// transaction.
			let current_block = <system::Pallet<T>>::block_number();
			<NextUnsignedAt<T>>::put(current_block + T::UnsignedInterval::get());
			Ok(().into())
		}

		#[pallet::call_index(4)]
		#[pallet::weight(0)]
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

		#[pallet::call_index(5)]
		#[pallet::weight(0)]
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

	#[pallet::validate_unsigned]
	impl<T: Config> ValidateUnsigned for Pallet<T> {
		type Call = Call<T>;

		/// Validate unsigned calls to this module.
		///
		/// By default, unsigned transactions are disallowed, but implementing
		/// this function we make sure that some particular calls are being
		/// whitelisted and marked as valid.
		///
		/// ⚠ WARNING ⚠ Anyone could be sending these unsigned transactions, not
		/// only OCWs!
		///
		/// When it comes to signed payloads, **we only check if the signature
		/// is coherent with the signer, but we don't really check if the signer
		/// is an authorized OCW**!
		///
		/// You should not interpret signed payloads as a filter that only
		/// allows transactions from authorized OCWs. Anyone could have signed
		/// those payloads, even malicious actors trying to "impersonate" an
		/// OCW.
		///
		/// There are NO implicit security assumptions here!
		fn validate_unsigned(_source: TransactionSource, call: &Self::Call) -> TransactionValidity {
			// Firstly let's check that we call the right function.
			if let Call::pong_unsigned_with_signed_payload {
				pong_payload: ref payload,
				ref signature,
			} = call
			{
				// ⚠ WARNING ⚠ this is nothing but a "sanity check" on the
				// signature it only checks if the signature is coherent with
				// the public key of `SignedPayload` whoever that might be (not
				// necessarily an authorized OCW)
				let signature_valid =
					SignedPayload::<T>::verify::<T::AuthorityId>(payload, signature.clone());
				if !signature_valid {
					return InvalidTransaction::BadProof.into()
				}
				Self::validate_transaction_parameters(&payload.block_number)
			} else if let Call::pong_unsigned { block_number, nonce: _n } = call {
				Self::validate_transaction_parameters(block_number)
			} else {
				InvalidTransaction::Call.into()
			}
		}
	}

	/// Container for different types that implement [`DefaultConfig`]` of this pallet.
	pub mod config_preludes {
		// This will help use not need to disambiguate anything when using `derive_impl`.
		use super::*;

		/// A type providing default configurations for this pallet in testing environment.
		pub struct TestDefaultConfig;
		const UNSIGNED_PRIORITY: u64 = 1 << 20;

		#[frame_support::register_default_impl(TestDefaultConfig)]
		impl DefaultConfig for TestDefaultConfig {
			type UnsignedPriority = frame_support::traits::ConstU64<UNSIGNED_PRIORITY>;
			type MaxPings = frame_support::traits::ConstU32<64>;
			type MaxAuthorities = frame_support::traits::ConstU32<64>;
		}
	}
}

/// Payload used by this example crate to hold pong response data required to
/// submit an unsigned transaction.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, scale_info::TypeInfo)]
pub struct PongPayload<Public, BlockNumber> {
	block_number: BlockNumber,
	nonce: u32,
	public: Public,
}

impl<T: SigningTypes> SignedPayload<T> for PongPayload<T::Public, BlockNumberFor<T>> {
	fn public(&self) -> T::Public {
		self.public.clone()
	}
}

impl<T: Config> Pallet<T> {
	fn is_authority(who: &T::AccountId) -> bool {
		<Authorities<T>>::get().contains(who)
	}

	fn validate_transaction_parameters(block_number: &BlockNumberFor<T>) -> TransactionValidity {
		// Now let's check if the transaction has any chance to succeed.
		let next_unsigned_at = <NextUnsignedAt<T>>::get();
		if &next_unsigned_at > block_number {
			return InvalidTransaction::Stale.into()
		}
		// Let's make sure to reject transactions from the future.
		let current_block = <system::Pallet<T>>::block_number();
		if &current_block < block_number {
			return InvalidTransaction::Future.into()
		}

		ValidTransaction::with_tag_prefix("ExampleOffchainWorker")
			// We set base priority to 2**20 and hope it's included before any
			// other transactions in the pool.
			.priority(T::UnsignedPriority::get().saturating_add(0))
			// This transaction does not require anything else to go before into
			// the pool. In theory we could require `previous_unsigned_at`
			// transaction to go first, but it's not necessary in our case.
			//.and_requires() We set the `provides` tag to be the same as
			// `next_unsigned_at`. This makes sure only one transaction produced
			// after `next_unsigned_at` will ever get to the transaction pool
			// and will end up in the block. We can still have multiple
			// transactions compete for the same "spot", and the one with higher
			// priority will replace other one in the pool.
			.and_provides(next_unsigned_at)
			// The transaction is only valid for next 5 blocks. After that it's
			// going to be revalidated by the pool.
			.longevity(5)
			// It's fine to propagate that transaction to other peers, which
			// means it can be created even by nodes that don't produce blocks.
			// Note that sometimes it's better to keep it for yourself (if you
			// are the block producer), since for instance in some schemes
			// others may copy your solution and claim a reward.
			.propagate(true)
			.build()
	}

	/// A helper function to send a signed pong transaction from the OCW.
	fn ocw_pong_signed() -> Result<(), &'static str> {
		let signer = Signer::<T, T::AuthorityId>::all_accounts();
		if !signer.can_sign() {
			return Err(
				"No local accounts available. Consider adding one via `author_insertKey` RPC.",
			)
		}

		let pings = <Pings<T>>::get();
		for p in pings {
			let Ping(nonce) = p;

			// Using `send_signed_transaction` associated type we create and
			// submit a transaction representing the call, we've just created.
			// Submit signed will return a vector of results for all accounts
			// that were found in the local keystore with expected `KEY_TYPE`.
			let results = signer.send_signed_transaction(|_account| {
				// nonce is wrapped into a call to `pong_signed` public function
				// of this pallet. This means that the transaction, when
				// executed, will simply call that function passing `nonce` as
				// an argument.
				Call::pong_signed { nonce }
			});

			for (acc, res) in &results {
				match res {
					Ok(()) => log::info!("[{:?}] Submitted pong with nonce {}", acc.id, nonce),
					Err(e) => log::error!("[{:?}] Failed to submit transaction: {:?}", acc.id, e),
				}
			}
		}

		Ok(())
	}

	/// A helper function to sign payload and send an unsigned pong transaction
	fn ocw_pong_unsigned_for_any_account(
		block_number: BlockNumberFor<T>,
	) -> Result<(), &'static str> {
		let pings = <Pings<T>>::get();
		for p in pings {
			let Ping(nonce) = p;

			// -- Sign using any account
			let (_, result) = Signer::<T, T::AuthorityId>::any_account()
				.send_unsigned_transaction(
					|account| PongPayload { nonce, block_number, public: account.public.clone() },
					|payload, signature| Call::pong_unsigned_with_signed_payload {
						pong_payload: payload,
						signature,
					},
				)
				.ok_or("No local accounts accounts available.")?;
			result.map_err(|()| "Unable to submit transaction")?;
		}

		Ok(())
	}

	/// A helper function to sign payload and send an unsigned pong transaction
	fn ocw_pong_unsigned_for_all_accounts(
		block_number: BlockNumberFor<T>,
	) -> Result<(), &'static str> {
		let pings = <Pings<T>>::get();
		for p in pings {
			let Ping(nonce) = p;

			// -- Sign using all accounts
			let transaction_results = Signer::<T, T::AuthorityId>::all_accounts()
				.send_unsigned_transaction(
					|account| PongPayload { nonce, block_number, public: account.public.clone() },
					|payload, signature| Call::pong_unsigned_with_signed_payload {
						pong_payload: payload,
						signature,
					},
				);
			for (_account_id, result) in transaction_results.into_iter() {
				if result.is_err() {
					return Err("Unable to submit transaction")
				}
			}
		}

		Ok(())
	}

	/// A helper function to send a raw unsigned pong transaction.
	fn ocw_pong_raw_unsigned(block_number: BlockNumberFor<T>) -> Result<(), &'static str> {
		let pings = <Pings<T>>::get();
		for p in pings {
			let Ping(nonce) = p;
			// nonce is wrapped into a call to `pong_unsigned` public function
			// of this pallet. This means that the transaction, when executed,
			// will simply call that function passing `nonce` as an argument.
			let call = Call::pong_unsigned { block_number, nonce };

			// Now let's create a transaction out of this call and submit it to
			// the pool. Here we showcase two ways to send an unsigned
			// transaction / unsigned payload (raw)
			//
			// By default unsigned transactions are disallowed, so we need to
			// whitelist this case by writing `UnsignedValidator`. Note that
			// it's EXTREMELY important to carefuly implement unsigned
			// validation logic, as any mistakes can lead to opening DoS or spam
			// attack vectors. See validation logic docs for more details.
			SubmitTransaction::<T, Call<T>>::submit_unsigned_transaction(call.into())
				.map_err(|()| "Unable to submit unsigned transaction.")?;
		}

		Ok(())
	}
}
