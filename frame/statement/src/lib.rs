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

#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::{
	pallet_prelude::*,
	sp_runtime::{traits::Zero, SaturatedConversion},
	sp_tracing::{enter_span, Level},
	traits::Currency,
};
use frame_system::pallet_prelude::*;
use sp_statement_store::{
	runtime_api::{InvalidStatement, StatementSource, ValidStatement},
	Proof, SignatureVerificationResult, Statement,
};

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

pub use pallet::*;

const LOG_TARGET: &str = "runtime::statement";

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	pub type BalanceOf<T> =
		<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

	#[pallet::config]
	pub trait Config: frame_system::Config
	where
		<Self as frame_system::Config>::AccountId: From<sp_statement_store::AccountId>,
	{
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
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
		<T as frame_system::Config>::AccountId: From<sp_statement_store::AccountId>,
	{
		/// A new statement is submitted
		NewStatement { account: T::AccountId, statement: Statement },
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T>
	where
		<T as frame_system::Config>::AccountId: From<sp_statement_store::AccountId>,
		sp_statement_store::AccountId: From<<T as frame_system::Config>::AccountId>,
		<T as frame_system::Config>::RuntimeEvent: From<pallet::Event<T>>,
		<T as frame_system::Config>::RuntimeEvent: TryInto<pallet::Event<T>>,
		sp_statement_store::BlockHash: From<<T as frame_system::Config>::Hash>,
	{
		fn offchain_worker(now: BlockNumberFor<T>) {
			log::trace!(target: LOG_TARGET, "Collecting statements at #{:?}", now);
			Pallet::<T>::collect_statements();
			Pallet::<T>::dispatch_statemens();
		}
	}
}

impl<T: Config> Pallet<T>
where
	<T as frame_system::Config>::AccountId: From<sp_statement_store::AccountId>,
	sp_statement_store::AccountId: From<<T as frame_system::Config>::AccountId>,
	<T as frame_system::Config>::RuntimeEvent: From<pallet::Event<T>>,
	<T as frame_system::Config>::RuntimeEvent: TryInto<pallet::Event<T>>,
	sp_statement_store::BlockHash: From<<T as frame_system::Config>::Hash>,
{
	/// Validate a statement against current state. This is supposed ti be called by the statement
	/// store on the host side.
	pub fn validate_statement(
		_source: StatementSource,
		mut statement: Statement,
	) -> Result<ValidStatement, InvalidStatement> {
		sp_io::init_tracing();

		enter_span! { Level::TRACE, "validate_statement" };
		log::debug!(target: LOG_TARGET, "Validating statement {:?}", statement);
		let account: T::AccountId = match statement.proof() {
			Some(Proof::OnChain { who, block_hash, event_index }) => {
				// block_hash and event_index should be checked by the host
				if frame_system::Pallet::<T>::parent_hash().as_ref() != block_hash.as_slice() {
					log::debug!(target: LOG_TARGET, "Bad block hash.");
					return Err(InvalidStatement::BadProof)
				}
				let account: T::AccountId = who.clone().into();
				match frame_system::Pallet::<T>::event_no_consensus(*event_index as usize) {
					Some(e) => {
						statement.strip_proof();
						if let Ok(Event::NewStatement { account: a, statement: s }) = e.try_into() {
							if a != account || s != statement {
								log::debug!(target: LOG_TARGET, "Event data mismatch");
								return Err(InvalidStatement::BadProof)
							}
						} else {
							log::debug!(target: LOG_TARGET, "Event type mismatch");
							return Err(InvalidStatement::BadProof)
						}
					},
					_ => {
						log::debug!(target: LOG_TARGET, "Bad event index");
						return Err(InvalidStatement::BadProof)
					},
				}
				account
			},
			_ => match statement.verify_signature() {
				SignatureVerificationResult::Valid(account) => account.into(),
				SignatureVerificationResult::Invalid => {
					log::debug!(target: LOG_TARGET, "Bad statement signature.");
					return Err(InvalidStatement::BadProof)
				},
				SignatureVerificationResult::NoSignature => {
					log::debug!(target: LOG_TARGET, "Missing statement signature.");
					return Err(InvalidStatement::NoProof)
				},
			},
		};
		let priority_cost = T::PriorityBalance::get();
		let priority: u64 = if priority_cost.is_zero() {
			0
		} else {
			let balance = T::Currency::free_balance(&account);
			let priority = balance / priority_cost;
			priority.saturated_into()
		};

		Ok(ValidStatement { priority })
	}

	/// Submit a statement event. The statement will be picked up by the offchain worker and
	/// broadcast to the network.
	pub fn submit_statement(account: T::AccountId, statement: Statement) {
		Self::deposit_event(Event::NewStatement { account, statement });
	}

	fn collect_statements() {
		// Find `NewStatement` events and submit them to the store
		for (index, event) in frame_system::Pallet::<T>::read_events_no_consensus().enumerate() {
			if let Ok(Event::<T>::NewStatement { account, mut statement }) = event.event.try_into()
			{
				if statement.proof().is_none() {
					let proof = Proof::OnChain {
						who: account.into(),
						block_hash: frame_system::Pallet::<T>::parent_hash().into(),
						event_index: index as u64,
					};
					statement.set_proof(proof);
				}
				sp_statement_store::runtime_api::io::submit_statement(statement);
			}
		}
	}

	fn dispatch_statemens() {
		let all_statements = sp_statement_store::runtime_api::io::dump();
		for (hash, _statement) in all_statements {
			// TODO: Custom statement handling
			log::trace!(target: LOG_TARGET, "Handling statement #{:?}", hash);
		}
	}
}
