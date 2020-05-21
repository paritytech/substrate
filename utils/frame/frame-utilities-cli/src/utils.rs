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
	MultiSigner, AccountId32, 
	traits::IdentifyAccount,
	generic::{UncheckedExtrinsic, SignedPayload},
};
use codec::Encode;
use frame_utils::{SignedExtensionProvider, IndexFor};

/// create an extrinsic for the runtime.
pub fn create_extrinsic_for<Pair, P, Call>(
	call: Call,
	nonce:  IndexFor<P>,
	signer: Pair,
) -> Result<UncheckedExtrinsic<AccountId32, Call, Pair::Signature, P::Extra>, &'static str>
	where
		Call: Encode,
		Pair: sp_core::Pair,
		Pair::Public: Into<MultiSigner>,
		Pair::Signature: Encode,
		P: SignedExtensionProvider,
{
	let extra = P::construct_extras(nonce);
	let payload = SignedPayload::new(call, extra)
		.map_err(|_| "Transaction validity error")?;

	let signature = payload.using_encoded(|payload| signer.sign(payload));
	let signer = signer.public().into().into_account();
	let (function, extra, _) = payload.deconstruct();

	Ok(UncheckedExtrinsic::new_signed(
		function,
		signer,
		signature,
		extra,
	))
}
