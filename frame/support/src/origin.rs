use crate::{
	error::BadOrigin,
	traits::{EnsureOrigin, SortedMembers},
	RuntimeDebug,
};
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

pub struct EnsureRoot<AccountId>(sp_std::marker::PhantomData<AccountId>);
impl<O: Into<Result<BaseOrigin<AccountId>, O>> + From<BaseOrigin<AccountId>>, AccountId>
	EnsureOrigin<O> for EnsureRoot<AccountId>
{
	type Success = ();
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			BaseOrigin::Root => Ok(()),
			r => Err(O::from(r)),
		})
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> O {
		O::from(BaseOrigin::Root)
	}
}

pub struct EnsureSigned<AccountId>(sp_std::marker::PhantomData<AccountId>);
impl<
		O: Into<Result<BaseOrigin<AccountId>, O>> + From<BaseOrigin<AccountId>>,
		AccountId: Decode,
	> EnsureOrigin<O> for EnsureSigned<AccountId>
{
	type Success = AccountId;
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			BaseOrigin::Signed(who) => Ok(who),
			r => Err(O::from(r)),
		})
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> O {
		let zero_account_id =
			AccountId::decode(&mut sp_runtime::traits::TrailingZeroInput::zeroes())
				.expect("infinite length input; no invalid inputs for type; qed");
		O::from(BaseOrigin::Signed(zero_account_id))
	}
}

pub struct EnsureSignedBy<Who, AccountId>(sp_std::marker::PhantomData<(Who, AccountId)>);
impl<
		O: Into<Result<BaseOrigin<AccountId>, O>> + From<BaseOrigin<AccountId>>,
		Who: SortedMembers<AccountId>,
		AccountId: PartialEq + Clone + Ord + Decode,
	> EnsureOrigin<O> for EnsureSignedBy<Who, AccountId>
{
	type Success = AccountId;
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			BaseOrigin::Signed(ref who) if Who::contains(who) => Ok(who.clone()),
			r => Err(O::from(r)),
		})
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> O {
		let zero_account_id =
			AccountId::decode(&mut sp_runtime::traits::TrailingZeroInput::zeroes())
				.expect("infinite length input; no invalid inputs for type; qed");
		let members = Who::sorted_members();
		let first_member = match members.get(0) {
			Some(account) => account.clone(),
			None => zero_account_id,
		};
		O::from(BaseOrigin::Signed(first_member.clone()))
	}
}

pub struct EnsureNone<AccountId>(sp_std::marker::PhantomData<AccountId>);
impl<O: Into<Result<BaseOrigin<AccountId>, O>> + From<BaseOrigin<AccountId>>, AccountId>
	EnsureOrigin<O> for EnsureNone<AccountId>
{
	type Success = ();
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			BaseOrigin::None => Ok(()),
			r => Err(O::from(r)),
		})
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> O {
		O::from(BaseOrigin::None)
	}
}

pub struct EnsureNever<T>(sp_std::marker::PhantomData<T>);
impl<O, T> EnsureOrigin<O> for EnsureNever<T> {
	type Success = T;
	fn try_origin(o: O) -> Result<Self::Success, O> {
		Err(o)
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> O {
		unimplemented!()
	}
}
