// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

use sp_runtime::{
	generic::{UncheckedExtrinsic, SignedPayload},
	MultiSigner, AccountId32, traits::IdentifyAccount, MultiSignature,
};
use codec::Encode;
use frame_system::extras::{
	SignedExtensionProvider, SystemExtraParams,
	IndexFor, AddressFor, AccountIdFor, SignedExtensionData,
};
use sp_runtime::generic::Era;

/// create an extrinsic for the runtime.
pub fn create_extrinsic_for<Pair, P, Call>(
	call: Call,
	nonce: IndexFor<P>,
	pair: Pair,
	hash: P::Hash,
) -> Result<
		UncheckedExtrinsic<AddressFor<P>, Call, MultiSignature, P::Extra>,
		&'static str
	>
	where
		Call: Encode,
		Pair: sp_core::Pair,
		Pair::Public: Into<MultiSigner>,
		Pair::Signature: Into<MultiSignature>,
		P: SignedExtensionProvider + pallet_indices::Trait,
		AccountIdFor<P>: From<AccountId32>,
		AddressFor<P>: From<AccountIdFor<P>>,
{
	let mut input = P::extension_params();
	input.set_nonce(nonce);
	input.set_era(Era::Immortal);
	input.set_prior_block_hash(hash);
	let SignedExtensionData { extra, additional } = P::construct_extras(input)?;

	let payload = if let Some(additional_signed) = additional {
		SignedPayload::from_raw(call, extra, additional_signed)
	} else {
		SignedPayload::new(call, extra)
			.map_err(|_| "Transaction validity error")?
	};

	let signer = pair.public().into().into_account();
	let account_id: AccountIdFor<P> = From::from(signer.clone());
	let address = AddressFor::<P>::from(account_id);

	let signature = payload.using_encoded(|payload| pair.sign(payload).into());
	let (function, extra, _) = payload.deconstruct();

	Ok(UncheckedExtrinsic::new_signed(
		function,
		address,
		signature,
		extra,
	))
}
