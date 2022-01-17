use crate::{error::BadOrigin, RuntimeDebug};
use codec::{Decode, Encode};
use scale_info::TypeInfo;

/// Origin for the System pallet.
#[derive(PartialEq, Eq, Clone, RuntimeDebug, Encode, Decode, TypeInfo)]
pub enum BaseOrigin<AccountId> {
	/// The system itself ordained this dispatch to happen: this is the highest privilege level.
	Root,
	/// It is signed by some public key and we provide the `AccountId`.
	Signed(AccountId),
	/// It is signed by nobody, can be either:
	/// * included and agreed upon by the validators anyway,
	/// * or unsigned transaction validated by a pallet.
	None,
}

impl<AccountId> From<Option<AccountId>> for BaseOrigin<AccountId> {
	fn from(s: Option<AccountId>) -> BaseOrigin<AccountId> {
		match s {
			Some(who) => BaseOrigin::Signed(who),
			None => BaseOrigin::None,
		}
	}
}

/// Ensure that the origin `o` represents a signed extrinsic (i.e. transaction).
/// Returns `Ok` with the account that signed the extrinsic or an `Err` otherwise.
pub fn ensure_signed<OuterOrigin, AccountId>(o: OuterOrigin) -> Result<AccountId, BadOrigin>
where
	OuterOrigin: Into<Result<BaseOrigin<AccountId>, OuterOrigin>>,
{
	match o.into() {
		Ok(BaseOrigin::Signed(t)) => Ok(t),
		_ => Err(BadOrigin),
	}
}

/// Ensure that the origin `o` represents either a signed extrinsic (i.e. transaction) or the root.
/// Returns `Ok` with the account that signed the extrinsic, `None` if it was root,  or an `Err`
/// otherwise.
pub fn ensure_signed_or_root<OuterOrigin, AccountId>(
	o: OuterOrigin,
) -> Result<Option<AccountId>, BadOrigin>
where
	OuterOrigin: Into<Result<BaseOrigin<AccountId>, OuterOrigin>>,
{
	match o.into() {
		Ok(BaseOrigin::Root) => Ok(None),
		Ok(BaseOrigin::Signed(t)) => Ok(Some(t)),
		_ => Err(BadOrigin),
	}
}

/// Ensure that the origin `o` represents the root. Returns `Ok` or an `Err` otherwise.
pub fn ensure_root<OuterOrigin, AccountId>(o: OuterOrigin) -> Result<(), BadOrigin>
where
	OuterOrigin: Into<Result<BaseOrigin<AccountId>, OuterOrigin>>,
{
	match o.into() {
		Ok(BaseOrigin::Root) => Ok(()),
		_ => Err(BadOrigin),
	}
}

/// Ensure that the origin `o` represents an unsigned extrinsic. Returns `Ok` or an `Err` otherwise.
pub fn ensure_none<OuterOrigin, AccountId>(o: OuterOrigin) -> Result<(), BadOrigin>
where
	OuterOrigin: Into<Result<BaseOrigin<AccountId>, OuterOrigin>>,
{
	match o.into() {
		Ok(BaseOrigin::None) => Ok(()),
		_ => Err(BadOrigin),
	}
}
