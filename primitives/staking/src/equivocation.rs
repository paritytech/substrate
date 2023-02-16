use crate::offence::{Offence, OffenceError, ReportOffence};
use sp_core::Get;
use sp_runtime::{DispatchError, DispatchResult};
use sp_std::vec::Vec;

pub trait EquivocationHandler {
	/// The longevity, in blocks, that the equivocation report is valid for. When using the staking
	/// pallet this should be equal to the bonding duration (in blocks, not eras).
	type ReportLongevity: Get<u64>;

	type AccountId;

	type Offence: Offence<Self::KeyOwnerIdentification>;

	type KeyOwnerIdentification;

	type EquivocationProof;

	type KeyOwnerProof;

	type ReportOffence: ReportOffence<Self::AccountId, Self::KeyOwnerIdentification, Self::Offence>;

	fn report_offence(
		reporters: Vec<Self::AccountId>,
		offence: Self::Offence,
	) -> Result<(), OffenceError> {
		Self::ReportOffence::report_offence(reporters, offence)
	}

	fn is_known_offence(
		offenders: &[Self::KeyOwnerIdentification],
		time_slot: &<Self::Offence as Offence<Self::KeyOwnerIdentification>>::TimeSlot,
	) -> bool {
		Self::ReportOffence::is_known_offence(offenders, time_slot)
	}

	/// Create and dispatch an equivocation report extrinsic.
	fn submit_unsigned_equivocation_report(
		_equivocation_proof: Self::EquivocationProof,
		_key_owner_proof: Self::KeyOwnerProof,
	) -> DispatchResult {
		Err(DispatchError::Other("Not implemented"))
	}

	/// Fetch the current block author id, if defined.
	fn block_author() -> Option<Self::AccountId> {
		None
	}
}

// impl<T: Offence<Id>, Id> EquivocationHandler for () {
// 	type ReportLongevity = ();

// 	type AccountId = ();

// 	type Offence = T; // Offence<Self::KeyOwnerIdentification>;

// 	type KeyOwnerIdentification = Id;

// 	type EquivocationProof = ();

// 	type KeyOwnerProof = ();

// 	type ReportOffence = ();
// }
