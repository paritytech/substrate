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

//! Supporting pallet for the statement store.
//!
//! - [`Pallet`]
//!
//! ## Overview
//!
//! The Statement pallet provides means to create and validate statements for the statement store.
//!

#![cfg_attr(not(feature = "std"), no_std)]

//use codec::{Decode, Encode, MaxEncodedLen};
use sp_statement_store::{Proof, Statement};
use sp_statement_store::runtime_api::{StatementSource, ValidStatement, InvalidStatement};
use frame_support::sp_tracing::{enter_span, Level};
use frame_support::sp_runtime::traits::{Zero, Verify};
use frame_support::sp_runtime::SaturatedConversion;
use frame_support::traits::Currency;
use frame_support::pallet_prelude::*;

//mod mock;
//mod tests;

pub use pallet::*;

const LOG_TARGET: &str = "runtime::statement";


#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::config]
	pub trait Config: frame_system::Config
	where
		<Self as frame_system::Config>::AccountId: From<[u8; 32]>,
	{
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>>
			+ IsType<<Self as frame_system::Config>::RuntimeEvent>;
		/// Account balance.
		type Currency: Currency<<Self as frame_system::Config>::AccountId>;
		/// Min balance for priority statements.
		#[pallet::constant]
		type PriorityBalance: Get<BalanceOf<Self>>;
	}

	#[pallet::pallet]
	pub struct Pallet<T>(sp_std::marker::PhantomData<T>);

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config>
	where
		<T as frame_system::Config>::AccountId: From<[u8; 32]>,
	{
		/// A new statement is submitted
		NewStatement { statement: Statement },
	}
	pub type BalanceOf<T> =
		<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
}

impl<T: Config> Pallet<T>
	where
		<T as frame_system::Config>::AccountId: From<[u8; 32]>,
		<T as frame_system::Config>::RuntimeEvent: From<pallet::Event<T>>,
{

	/// Validate a statement against current state. This is supposed ti be called by the statement
	/// store on the host side.
	pub fn validate_statement(
		_source: StatementSource,
		statement: Statement,
	) -> Result<ValidStatement, InvalidStatement> {
		sp_io::init_tracing();

		enter_span! { Level::TRACE, "validate_statement" };
		log::debug!(target: LOG_TARGET, "Validating statement {:?}", statement);
		let account: Option<T::AccountId> = match statement.proof() {
			None => None,
			Some(Proof::Sr25519 { signature, signer }) => {
				let to_sign = statement.signature_material();
				let signature =  sp_core::sr25519::Signature(*signature);
				let public = sp_core::sr25519::Public(*signer);
				if !signature.verify(to_sign.as_slice(), &public) {
					log::debug!(target: LOG_TARGET, "Bad Sr25519 signature.");
					return Err(InvalidStatement::BadProof);
				}
				Some(signer.clone().into())
			},
			Some(Proof::Ed25519 { signature, signer }) => {
				let to_sign = statement.signature_material();
				let signature =  sp_core::ed25519::Signature(*signature);
				let public = sp_core::ed25519::Public(*signer);
				if !signature.verify(to_sign.as_slice(), &public) {
					log::debug!(target: LOG_TARGET, "Bad Ed25519 signature.");
					return Err(InvalidStatement::BadProof);
				}
				Some(signer.clone().into())
			},
			Some(Proof::Secp256k1Ecdsa { signature, signer }) => {
				let to_sign = statement.signature_material();
				let signature =  sp_core::ecdsa::Signature(*signature);
				let public = sp_core::ecdsa::Public(*signer);
				if !signature.verify(to_sign.as_slice(), &public) {
					log::debug!(target: LOG_TARGET, "Bad ECDSA signature.");
					return Err(InvalidStatement::BadProof);
				}
				Some(sp_io::hashing::blake2_256(signer).into())
			},
			Some(Proof::OnChain { who, block_hash, event_index }) => {
				// block_hash and event_index should be checked by the host
				if frame_system::Pallet::<T>::parent_hash().as_ref() != block_hash.as_slice() {
					log::debug!(target: LOG_TARGET, "Bad block hash.");
					return Err(InvalidStatement::BadProof);
				}
				let account_id = Some(who.clone().into());
				match frame_system::Pallet::<T>::event_no_consensus(*event_index as usize) {
					Some(e) => {
						if e != (Event::NewStatement { statement: statement.strip_proof() }).into() {
							log::debug!(target: LOG_TARGET, "Event mismatch");
							return Err(InvalidStatement::BadProof);
						}
					},
					_ => {
						log::debug!(target: LOG_TARGET, "Bad event index");
						return Err(InvalidStatement::BadProof);
					}
				}
				account_id
			}
		};
		let priority: u64 = if let Some(account) = account {
			let priority_cost = T::PriorityBalance::get();
			if priority_cost.is_zero() {
				0
			}
			else {
				let balance = T::Currency::free_balance(&account);
				let priority = balance / priority_cost;
				priority.saturated_into()

			}
		} else {
			0
		};

		Ok(ValidStatement {
			priority,
			propagate: true,
		})
	}

	pub fn submit_statement(statement: Statement) {
		Self::deposit_event(Event::NewStatement { statement });
	}

}

