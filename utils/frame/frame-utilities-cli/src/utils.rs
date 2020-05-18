// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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
use sp_runtime::{
	MultiSigner, AccountId32, 
	traits::IdentifyAccount,
	generic::{UncheckedExtrinsic, SignedPayload},
};
use codec::Encode;
use cli_utils::{RuntimeAdapter, IndexFor};

/// create an extrinsic for the runtime.
pub fn create_extrinsic_for<Pair, RA, Call>(
	call: Call,
	nonce:  IndexFor<RA>,
	signer: Pair,
) -> Result<UncheckedExtrinsic<AccountId32, Call, Pair::Signature, RA::Extra>, &'static str>
	where
		Call: Encode,
		Pair: sp_core::Pair,
		Pair::Public: Into<MultiSigner>,
		Pair::Signature: Encode,
		RA: RuntimeAdapter,
{
	let extra = RA::build_extra(nonce);
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
