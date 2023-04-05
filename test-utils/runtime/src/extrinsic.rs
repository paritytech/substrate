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
	substrate_test_pallet, substrate_test_pallet::pallet::Call as PalletCall,
	AuthorityId, CheckSubstrateCall, Index, Extrinsic, Pair, RuntimeCall, Signature, SignedExtra, SignedPayload, Transfer,
};
use codec::Encode;
use frame_system::{CheckWeight, CheckNonce};
use sp_core::crypto::Pair as TraitPair;
use sp_runtime::{Perbill, transaction_validity::{InvalidTransaction, TransactionValidityError}};
use sp_std::prelude::*;

impl Transfer {
	/// Convert into a signed unchecked extrinsic.
	pub fn into_unchecked_extrinsic(self) -> Extrinsic {
		let nonce = self.nonce;
		ExtrinsicBuilder::new_transfer(self).build2(nonce)
	}

	/// If feasible extract `Transfer` from given `Extrinsic`
	pub fn try_from_unchecked_extrinsic(uxt: &Extrinsic) -> Option<Self> {
		if let RuntimeCall::SubstrateTest(ref test_pallet_call) = uxt.function {
			if let PalletCall::transfer { transfer, .. } = test_pallet_call {
				return Some(transfer.clone())
			}
			return None
		}
		None
	}

	/// Verify signature and extracts `Transfer` from given `Extrinsic`, otherwise returns
	/// error
	pub fn try_from_unchecked_extrinsic_and_verify(
		uxt: &Extrinsic,
	) -> Result<Self, TransactionValidityError> {
		if let RuntimeCall::SubstrateTest(PalletCall::transfer {
			ref transfer,
			ref signature,
			..
		}) = uxt.function
		{
			if sp_runtime::verify_encoded_lazy(signature, transfer, &transfer.from) {
				Ok(transfer.clone())
			} else {
				Err(InvalidTransaction::BadProof.into())
			}
		} else {
			Err(InvalidTransaction::Call.into())
		}
	}
}

/// Generate `PalletCall::transfer_call`
pub struct TransferCallBuilder {
	transfer: Transfer,
	signature: Option<Signature>,
	exhaust_resources: bool,
}

impl TransferCallBuilder {
	/// Create `Self` with given `transfer` value
	pub fn new(transfer: Transfer) -> Self {
		TransferCallBuilder { transfer, signature: None, exhaust_resources: false }
	}

	/// Sign `transfer` with `signer` and embeds signature into `PalletCall::transfer_call`
	pub fn signer(mut self, signer: Pair) -> Self {
		self.signature = Some(signer.sign(&self.transfer.encode()));
		self
	}

	/// Embed given signature into `PalletCall::transfer_call`
	pub fn with_signature(mut self, signature: Signature) -> Self {
		self.signature = Some(signature);
		self
	}

	/// Set `exhaust_resources` flag of `PalletCall::transfer_call` to true
	pub fn exhaust_resources(mut self) -> Self {
		self.exhaust_resources = true;
		self
	}

	/// Generate instance of `PalletCall::transfer_call`
	pub fn build<T: substrate_test_pallet::Config>(self) -> PalletCall<T> {
		let signature = match self.signature {
			Some(signature) => signature,
			None => sp_keyring::AccountKeyring::from_public(&self.transfer.from)
				.expect("Creates keyring from public key.")
				.sign(&self.transfer.encode()),
		};
		PalletCall::transfer {
			transfer: self.transfer,
			signature,
			exhaust_resources_when_not_first: self.exhaust_resources,
		}
	}
}

/// Generates `Extrinsic`
pub struct ExtrinsicBuilder {
	function: RuntimeCall,
	is_unsigned: bool,
	// signer: sp_keyring::AccountKeyring,
	signer: Pair,
}

impl ExtrinsicBuilder {
	/// Create builder for given `RuntimeCall`
	pub fn new(function: impl Into<RuntimeCall>) -> Self {
		Self { function: function.into(), is_unsigned: false, signer: sp_keyring::AccountKeyring::Alice.pair() }
	}

	/// Create builder for given `Transfer`
	pub fn new_transfer(transfer: Transfer) -> Self {
		Self::new(TransferCallBuilder::new(transfer).build())
	}

	/// Create builder for `PalletCall::authorities_change` call using given parameters
	pub fn new_authorities_change(new_authorities: Vec<AuthorityId>) -> Self {
		Self::new(PalletCall::authorities_change { new_authorities })
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

	/// Create builder for `pallet_root_testing::Call::new_deposit_log_digest_item`
	pub fn new_fill_block(ratio: Perbill) -> Self {
		Self::new(pallet_root_testing::Call::fill_block{ ratio } )
	}

	/// Unsigned `Extrinsic` will be created
	pub fn unsigned(mut self) -> Self {
		self.is_unsigned = true;
		self
	}

	pub fn signer(mut self, signer: Pair) -> Self {
		self.signer = signer;
		self
	}

	/// Build `Extrinsic` using embedded parameters
	pub fn build(self) -> Extrinsic {
		self.build2(0u32.into())
	}

	pub fn build2(self, nonce: Index) -> Extrinsic {
		if self.is_unsigned {
			Extrinsic::new_unsigned(self.function)
		} else {
			let signer = self.signer;
			let extra = (CheckNonce::from(nonce), CheckWeight::new(), CheckSubstrateCall{});
			let raw_payload = SignedPayload::from_raw(self.function.clone(), extra.clone(), ((),(),()));
			let signature = raw_payload.using_encoded(|e| signer.sign(e));

			Extrinsic::new_signed(self.function, signer.public(), signature, extra)
		}
	}
}
