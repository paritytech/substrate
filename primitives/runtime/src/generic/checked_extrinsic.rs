// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Generic implementation of an extrinsic that has passed the verification
//! stage.

use crate::{
	traits::{
		self, DispatchInfoOf, Dispatchable, FatCall, MaybeDisplay, Member, PostDispatchInfoOf,
		PreimageHandler, SignedExtension, ValidateUnsigned,
	},
	transaction_validity::{TransactionSource, TransactionValidity},
};

/// Definition of something that the external world might want to say; its
/// existence implies that it has been checked and is good, particularly with
/// regards to the signature.
#[derive(PartialEq, Eq, Clone, sp_core::RuntimeDebug)]
pub struct CheckedExtrinsic<AccountId, Call, Extra> {
	/// Who this purports to be from and the number of extrinsics have come before
	/// from the same signer, if anyone (note this is not a signature).
	pub signed: Option<(AccountId, Extra)>,

	/// The function that should be called. This should include everything needed for correct
	/// execution, and in the latest version includes data which the dispatchable relies on.
	pub function: FatCall<Call>,
}

impl<AccountId, Call, Extra, Origin> traits::Applyable for CheckedExtrinsic<AccountId, Call, Extra>
where
	AccountId: Member + MaybeDisplay,
	Call: Member + Dispatchable<Origin = Origin>,
	Extra: SignedExtension<AccountId = AccountId, Call = Call>,
	Origin: From<Option<AccountId>>,
{
	type Call = Call;

	fn validate<U: ValidateUnsigned<Call = Self::Call>, P: PreimageHandler>(
		&self,
		// TODO [#5006;ToDr] should source be passed to `SignedExtension`s?
		// Perhaps a change for 2.0 to avoid breaking too much APIs?
		source: TransactionSource,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> TransactionValidity {
		let FatCall { call, auxilliary_data: aux_data } = &self.function;
		if let Some((ref id, ref extra)) = self.signed {
			Extra::validate(extra, id, call, info, len, aux_data)
		} else {
			U::validate_aux_data(call, aux_data)?;
			let unsigned_validation = U::validate_unsigned(source, call, aux_data)?;
			let valid = Extra::validate_unsigned(call, info, len, aux_data)?;
			Ok(valid.combine_with(unsigned_validation))
		}
	}

	fn apply<U: ValidateUnsigned<Call = Self::Call>, P: PreimageHandler>(
		self,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> crate::ApplyExtrinsicResultWithInfo<PostDispatchInfoOf<Self::Call>> {
		let FatCall { call, auxilliary_data: aux_data } = self.function;
		let (maybe_who, maybe_pre) = if let Some((id, extra)) = self.signed {
			let pre = Extra::pre_dispatch(extra, &id, &call, info, len, &aux_data)?;
			(Some(id), Some(pre))
		} else {
			U::validate_aux_data(&call, &aux_data)?;
			U::pre_dispatch(&call, &aux_data)?;
			Extra::pre_dispatch_unsigned(&call, info, len, &aux_data)?;
			(None, None)
		};

		// Place the primage data.
		for data in aux_data.into_iter() {
			P::note_preimage(sp_std::borrow::Cow::from(data));
		}
		let res = call.dispatch(Origin::from(maybe_who));
		// Remove the primage data.
		P::clear();

		let post_info = match res {
			Ok(info) => info,
			Err(err) => err.post_info,
		};
		Extra::post_dispatch(
			maybe_pre,
			info,
			&post_info,
			len,
			&res.map(|_| ()).map_err(|e| e.error),
		)?;
		Ok(res)
	}
}
