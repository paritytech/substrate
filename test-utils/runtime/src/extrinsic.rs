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

use crate::{
	substrate_test_pallet::pallet::Call as PalletCall, AccountId, Balance, BalancesCall,
	CheckSubstrateCall, Extrinsic, Index, Pair, RuntimeCall, SignedPayload, TransferData,
};
use codec::Encode;
use frame_system::{CheckNonce, CheckWeight};
use sp_core::crypto::Pair as TraitPair;
use sp_runtime::{transaction_validity::TransactionPriority, Perbill};
use sp_std::prelude::*;

/// Transfer used in test substrate pallet. Extrinsic is created and signed basing on this data.
#[derive(Clone)]
pub struct Transfer {
	pub from: Pair,
	pub to: AccountId,
	pub amount: Balance,
	pub nonce: u64,
}

impl Transfer {
	/// Convert into a signed unchecked extrinsic.
	pub fn into_unchecked_extrinsic(self) -> Extrinsic {
		ExtrinsicBuilder::new_transfer(self).build()
	}
}

impl TransferData {
	/// If feasible extract `TransferData` from given `Extrinsic`
	pub fn try_from_unchecked_extrinsic(uxt: &Extrinsic) -> Option<Self> {
		match uxt {
			Extrinsic {
				function: RuntimeCall::Balances(BalancesCall::transfer_allow_death { dest, value }),
				signature: Some((from, _, (CheckNonce(nonce), ..))),
			} => Some(TransferData {
				from: from.clone(),
				to: dest.clone(),
				amount: *value,
				nonce: *nonce,
			}),
			Extrinsic {
				function: RuntimeCall::SubstrateTest(PalletCall::bench_call { transfer }),
				signature: None,
			} => Some(transfer.clone()),
			_ => None,
		}
	}
}

/// Generates `Extrinsic`
pub struct ExtrinsicBuilder {
	function: RuntimeCall,
	signer: Option<Pair>,
	nonce: Option<Index>,
}

impl ExtrinsicBuilder {
	/// Create builder for given `RuntimeCall`. By default `Extrinsic` will be signed by `Alice`.
	pub fn new(function: impl Into<RuntimeCall>) -> Self {
		Self {
			function: function.into(),
			signer: Some(sp_keyring::AccountKeyring::Alice.pair()),
			nonce: None,
		}
	}

	/// Create builder for `pallet_call::bench_transfer` from given `TransferData`.
	pub fn new_bench_call(transfer: TransferData) -> Self {
		Self { function: PalletCall::bench_call { transfer }.into(), signer: None, nonce: None }
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

	/// Create builder for `PalletCall::storage_change` call using given parameters
	pub fn new_storage_change(key: Vec<u8>, value: Option<Vec<u8>>) -> Self {
		Self::new(PalletCall::storage_change { key, value })
	}

	/// Create builder for `PalletCall::storage_change_unsigned` call using given parameters. Will
	/// create unsigned Extrinsic.
	pub fn new_storage_change_unsigned(key: Vec<u8>, value: Option<Vec<u8>>) -> Self {
		Self::new(PalletCall::storage_change_unsigned { key, value }).unsigned()
	}

	/// Create builder for `PalletCall::offchain_index_set` call using given parameters
	pub fn new_offchain_index_set(key: Vec<u8>, value: Vec<u8>) -> Self {
		Self::new(PalletCall::offchain_index_set { key, value })
	}

	/// Create builder for `PalletCall::offchain_index_clear` call using given parameters
	pub fn new_offchain_index_clear(key: Vec<u8>) -> Self {
		Self::new(PalletCall::offchain_index_clear { key })
	}

	/// Create builder for `PalletCall::new_store` call using given parameters
	pub fn new_store(data: Vec<u8>) -> Self {
		Self::new(PalletCall::store { data })
	}

	/// Create builder for `PalletCall::new_deposit_log_digest_item` call using given `log`
	pub fn new_deposit_log_digest_item(log: sp_runtime::generic::DigestItem) -> Self {
		Self::new(PalletCall::deposit_log_digest_item { log })
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

	/// Unsigned `Extrinsic` will be created
	pub fn unsigned(mut self) -> Self {
		self.signer = None;
		self
	}

	/// Given `nonce` will be set in `Extrinsic`
	pub fn nonce(mut self, nonce: Index) -> Self {
		self.nonce = Some(nonce);
		self
	}

	/// Extrinsic will be signed by signer
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
