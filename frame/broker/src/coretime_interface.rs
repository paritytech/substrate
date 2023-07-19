use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::Parameter;
use scale_info::TypeInfo;
use sp_arithmetic::traits::AtLeast32BitUnsigned;
use sp_core::RuntimeDebug;
use sp_std::{fmt::Debug, vec::Vec};

/// Index of a Polkadot Core.
pub type CoreIndex = u16;

/// A Task Id. In general this is called a ParachainId.
pub type TaskId = u32;

/// Fraction expressed as a nominator with an assumed denominator of 57,600.
pub type PartsOf57600 = u16;

/// An element to which a core can be assigned.
#[derive(
	Encode, Decode, Clone, Eq, PartialEq, Ord, PartialOrd, RuntimeDebug, TypeInfo, MaxEncodedLen,
)]
pub enum CoreAssignment {
	/// Core need not be used for anything.
	Idle,
	/// Core should be used for the Instantaneous Coretime Pool.
	Pool,
	/// Core should be used to process the given task.
	Task(TaskId),
}

pub trait CoretimeInterface {
	type AccountId: Parameter;
	type Balance;
	type BlockNumber: AtLeast32BitUnsigned
		+ Copy
		+ TypeInfo
		+ Encode
		+ Decode
		+ MaxEncodedLen
		+ Debug;
	fn latest() -> Self::BlockNumber;
	fn request_core_count(count: CoreIndex);
	fn request_revenue_info_at(when: Self::BlockNumber);
	fn credit_account(who: Self::AccountId, amount: Self::Balance);
	fn assign_core(
		core: CoreIndex,
		begin: Self::BlockNumber,
		assignment: Vec<(CoreAssignment, PartsOf57600)>,
		end_hint: Option<Self::BlockNumber>,
	);
	fn check_notify_core_count() -> Option<u16>;
	fn check_notify_revenue_info() -> Option<(Self::BlockNumber, Self::Balance)>;
}
impl CoretimeInterface for () {
	type AccountId = ();
	type Balance = u128;
	type BlockNumber = u32;
	fn latest() -> Self::BlockNumber {
		0
	}
	fn request_core_count(_count: CoreIndex) {}
	fn request_revenue_info_at(_when: Self::BlockNumber) {}
	fn credit_account(_who: Self::AccountId, _amount: Self::Balance) {}
	fn assign_core(
		_core: CoreIndex,
		_begin: Self::BlockNumber,
		_assignment: Vec<(CoreAssignment, PartsOf57600)>,
		_end_hint: Option<Self::BlockNumber>,
	) {
	}
	fn check_notify_core_count() -> Option<u16> {
		None
	}
	fn check_notify_revenue_info() -> Option<(Self::BlockNumber, Self::Balance)> {
		None
	}
}
