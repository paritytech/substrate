// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Generic implementation of an extrinsic that has passed the verification
//! stage.

use crate::traits::{
	self, Member, MaybeDisplay, SignedExtension, Dispatchable, DispatchInfoOf,
};
use crate::transaction_validity::{TransactionValidity, TransactionSource};

/// Definition of something that the external world might want to say; its
/// existence implies that it has been checked and is good, particularly with
/// regards to the signature.
#[derive(PartialEq, Eq, Clone, sp_core::RuntimeDebug)]
pub struct CheckedExtrinsic<AccountId, Call, Extra> {
	/// Who this purports to be from and the number of extrinsics have come before
	/// from the same signer, if anyone (note this is not a signature).
	pub signed: Option<(AccountId, Extra)>,

	/// The function that should be called.
	pub function: Call,
}

impl<AccountId, Call, Extra, Origin> traits::Applyable for
	CheckedExtrinsic<AccountId, Call, Extra>
where
	AccountId: Member + MaybeDisplay,
	Call: Member + Dispatchable<Origin=Origin>,
	Extra: SignedExtension<AccountId=AccountId, Call=Call>,
	Origin: From<Option<AccountId>>,
{
	type Call = Call;

	fn validate(
		&self,
		source: TransactionSource,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> TransactionValidity {
		if let Some((ref id, ref extra)) = self.signed {
			Extra::validate(extra, id, source, &self.function, info, len)
		} else {
			Extra::validate_unsigned(source, &self.function, info, len)
		}
	}

	fn apply(
		self,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> crate::ApplyExtrinsicResult {
		let (maybe_who, pre) = if let Some((id, extra)) = self.signed {
			let pre = Extra::pre_dispatch(extra, &id, &self.function, info, len)?;
			(Some(id), pre)
		} else {
			let pre = Extra::pre_dispatch_unsigned(&self.function, info, len)?;
			(None, pre)
		};
		let res = self.function.dispatch(Origin::from(maybe_who));
		let post_info = match res {
			Ok(info) => info,
			Err(err) => err.post_info,
		};
		let res = res.map(|_| ()).map_err(|e| e.error);
		Extra::post_dispatch(pre, info, &post_info, len, &res)?;
		Ok(res)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use traits::Applyable;
	use crate::transaction_validity::{
		TransactionValidityError, InvalidTransaction, ValidTransaction,
	};

	type AccountId = u32;
	#[derive(PartialEq, Eq, Clone, Copy, Debug)]
	struct Call;

	impl traits::Dispatchable for Call {
		type Origin = Option<AccountId>;
		type Trait = ();
		type PostInfo = ();
		type Info = ();

		fn dispatch(self, origin: Self::Origin) -> crate::DispatchResultWithInfo<Self::PostInfo> {
			origin
				.map(|_| ())
				.ok_or_else(|| panic!("Should not dispatch unsigned transactions."))
		}
	}

	#[derive(Debug, Eq, Clone, PartialEq, codec::Encode, codec::Decode)]
	struct Extra;
	impl SignedExtension for Extra {
		const IDENTIFIER: &'static str = "test";

		type AccountId = AccountId;
		type Call = Call;
		type AdditionalSigned = ();
		type Pre = ();

		fn additional_signed(&self) -> Result<Self::AdditionalSigned, TransactionValidityError> {
			Ok(())
		}

	}

	type Extrinsic = CheckedExtrinsic<AccountId, Call, (Extra, )>;

	fn extrinsics() -> (Extrinsic, Extrinsic) {
		let unsigned = Extrinsic {
			signed: None,
			function: Call,
		};
		let signed = Extrinsic {
			signed: Some((1, Extra)),
			function: Call,
		};
		(signed, unsigned)
	}

	fn is_applyable<T: Applyable>() {}

	#[test]
	fn should_allow_signed_and_forbid_unsigned_during_apply() {
		is_applyable::<Extrinsic>();
		let (signed, unsigned) = extrinsics();

		let res = signed.apply(&Default::default(), 1);
		assert_eq!(res.unwrap().unwrap(), ());
		let res = unsigned.apply(&Default::default(), 1);
		assert_eq!(res.unwrap_err(), InvalidTransaction::NoUnsignedValidator.into());
	}

	#[test]
	fn should_allow_signed_and_forbid_unsigned_during_validate() {
		is_applyable::<Extrinsic>();
		let (signed, unsigned) = extrinsics();
		let source = TransactionSource::External;

		let res = signed.validate(source, &Default::default(), 1);
		assert_eq!(res.unwrap(), ValidTransaction::default());
		let res = unsigned.validate(source, &Default::default(), 1);
		assert_eq!(res.unwrap_err(), InvalidTransaction::NoUnsignedValidator.into());
	}
}
