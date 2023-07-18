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

//! Provides utils for building the `Extrinsic` instances used with `substrate-test-runtime`.

use crate::{
	substrate_test_pallet::pallet::Call as PalletCall, AccountId, Balance, BalancesCall,
	CheckSubstrateCall, Extrinsic, Nonce, Pair, RuntimeCall, SignedPayload, TransferData,
};
use codec::Encode;
use frame_system::{CheckNonce, CheckWeight};
use sp_core::crypto::Pair as TraitPair;
use sp_keyring::AccountKeyring;
use sp_runtime::{transaction_validity::TransactionPriority, Perbill};
use sp_std::prelude::*;

/// Transfer used in test substrate pallet. Extrinsic is created and signed using this data.
#[derive(Clone)]
pub struct Transfer {
	/// Transfer sender and signer of created extrinsic
	pub from: Pair,
	/// The recipient of the transfer
	pub to: AccountId,
	/// Amount of transfer
	pub amount: Balance,
	/// Sender's account nonce at which transfer is valid
	pub nonce: u64,
}

impl Transfer {
	/// Convert into a signed unchecked extrinsic.
	pub fn into_unchecked_extrinsic(self) -> Extrinsic {
		ExtrinsicBuilder::new_transfer(self).build()
	}
}

impl Default for TransferData {
	fn default() -> Self {
		Self {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Bob.into(),
			amount: 0,
			nonce: 0,
		}
	}
}

/// If feasible converts given `Extrinsic` to `TransferData`
impl TryFrom<&Extrinsic> for TransferData {
	type Error = ();
	fn try_from(uxt: &Extrinsic) -> Result<Self, Self::Error> {
		match uxt {
			Extrinsic {
				function: RuntimeCall::Balances(BalancesCall::transfer_allow_death { dest, value }),
				signature: Some((from, _, (CheckNonce(nonce), ..))),
			} => Ok(TransferData { from: *from, to: *dest, amount: *value, nonce: *nonce }),
			Extrinsic {
				function: RuntimeCall::SubstrateTest(PalletCall::bench_call { transfer }),
				signature: None,
			} => Ok(transfer.clone()),
			_ => Err(()),
		}
	}
}

/// Generates `Extrinsic`
pub struct ExtrinsicBuilder {
	function: RuntimeCall,
	signer: Option<Pair>,
	nonce: Option<Nonce>,
}

impl ExtrinsicBuilder {
	/// Create builder for given `RuntimeCall`. By default `Extrinsic` will be signed by `Alice`.
	pub fn new(function: impl Into<RuntimeCall>) -> Self {
		Self { function: function.into(), signer: Some(AccountKeyring::Alice.pair()), nonce: None }
	}

	/// Create builder for given `RuntimeCall`. `Extrinsic` will be unsigned.
	pub fn new_unsigned(function: impl Into<RuntimeCall>) -> Self {
		Self { function: function.into(), signer: None, nonce: None }
	}

	/// Create builder for `pallet_call::bench_transfer` from given `TransferData`.
	pub fn new_bench_call(transfer: TransferData) -> Self {
		Self::new_unsigned(PalletCall::bench_call { transfer })
	}

	/// Create builder for given `Transfer`. Transfer `nonce` will be used as `Extrinsic` nonce.
	/// Transfer `from` will be used as Extrinsic signer.
	pub fn new_transfer(transfer: Transfer) -> Self {
		Self {
			nonce: Some(transfer.nonce),
			signer: Some(transfer.from.clone()),
			..Self::new(BalancesCall::transfer_allow_death {
				dest: transfer.to,
				value: transfer.amount,
			})
		}
	}

	/// Create builder for `PalletCall::include_data` call using given parameters
	pub fn new_include_data(data: Vec<u8>) -> Self {
		Self::new(PalletCall::include_data { data })
	}

	/// Create builder for `PalletCall::storage_change` call using given parameters. Will
	/// create unsigned Extrinsic.
	pub fn new_storage_change(key: Vec<u8>, value: Option<Vec<u8>>) -> Self {
		Self::new_unsigned(PalletCall::storage_change { key, value })
	}

	/// Create builder for `PalletCall::offchain_index_set` call using given parameters
	pub fn new_offchain_index_set(key: Vec<u8>, value: Vec<u8>) -> Self {
		Self::new(PalletCall::offchain_index_set { key, value })
	}

	/// Create builder for `PalletCall::offchain_index_clear` call using given parameters
	pub fn new_offchain_index_clear(key: Vec<u8>) -> Self {
		Self::new(PalletCall::offchain_index_clear { key })
	}

	/// Create builder for `PalletCall::indexed_call` call using given parameters
	pub fn new_indexed_call(data: Vec<u8>) -> Self {
		Self::new(PalletCall::indexed_call { data })
	}

	/// Create builder for `PalletCall::new_deposit_log_digest_item` call using given `log`
	pub fn new_deposit_log_digest_item(log: sp_runtime::generic::DigestItem) -> Self {
		Self::new_unsigned(PalletCall::deposit_log_digest_item { log })
	}

	/// Create builder for `PalletCall::Call::new_deposit_log_digest_item`
	pub fn new_fill_block(ratio: Perbill) -> Self {
		Self::new(PalletCall::fill_block { ratio })
	}

	/// Create builder for `PalletCall::call_do_not_propagate` call using given parameters
	pub fn new_call_do_not_propagate() -> Self {
		Self::new(PalletCall::call_do_not_propagate {})
	}

	/// Create builder for `PalletCall::call_with_priority` call using given parameters
	pub fn new_call_with_priority(priority: TransactionPriority) -> Self {
		Self::new(PalletCall::call_with_priority { priority })
	}

	/// Create builder for `PalletCall::read` call using given parameters
	pub fn new_read(count: u32) -> Self {
		Self::new_unsigned(PalletCall::read { count })
	}

	/// Create builder for `PalletCall::read` call using given parameters
	pub fn new_read_and_panic(count: u32) -> Self {
		Self::new_unsigned(PalletCall::read_and_panic { count })
	}

	/// Unsigned `Extrinsic` will be created
	pub fn unsigned(mut self) -> Self {
		self.signer = None;
		self
	}

	/// Given `nonce` will be set in `Extrinsic`
	pub fn nonce(mut self, nonce: Nonce) -> Self {
		self.nonce = Some(nonce);
		self
	}

	/// Extrinsic will be signed by `signer`
	pub fn signer(mut self, signer: Pair) -> Self {
		self.signer = Some(signer);
		self
	}

	/// Build `Extrinsic` using embedded parameters
	pub fn build(self) -> Extrinsic {
		if let Some(signer) = self.signer {
			let extra = (
				CheckNonce::from(self.nonce.unwrap_or(0)),
				CheckWeight::new(),
				CheckSubstrateCall {},
			);
			let raw_payload =
				SignedPayload::from_raw(self.function.clone(), extra.clone(), ((), (), ()));
			let signature = raw_payload.using_encoded(|e| signer.sign(e));

			Extrinsic::new_signed(self.function, signer.public(), signature, extra)
		} else {
			Extrinsic::new_unsigned(self.function)
		}
	}
}
