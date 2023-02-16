use crate::offence::{Offence, OffenceError, ReportOffence};
use sp_core::Get;
use sp_runtime::DispatchResult;
use sp_std::vec::Vec;

pub trait EquivocationHandler {
	type ReporterId;

	type OffenderId;

	type EquivocationProof;

	type KeyOwnerProof;

	type Offence: Offence<Self::OffenderId>;

	type ReportOffence: ReportOffence<Self::ReporterId, Self::OffenderId, Self::Offence>;

	/// The longevity, in blocks, that the equivocation report is valid for. When using the staking
	/// pallet this should be equal to the bonding duration (in blocks, not eras).
	type ReportLongevity: Get<u64>;

	fn report_offence(
		reporters: Vec<Self::ReporterId>,
		offence: Self::Offence,
	) -> Result<(), OffenceError> {
		Self::ReportOffence::report_offence(reporters, offence)
	}

	fn is_known_offence(
		offenders: &[Self::OffenderId],
		time_slot: &<Self::Offence as Offence<Self::OffenderId>>::TimeSlot,
	) -> bool {
		Self::ReportOffence::is_known_offence(offenders, time_slot)
	}

	/// Create and dispatch an equivocation report extrinsic.
	fn submit_unsigned_equivocation_report(
		_equivocation_proof: Self::EquivocationProof,
		_key_owner_proof: Self::KeyOwnerProof,
	) -> DispatchResult {
		Ok(())
	}

	/// Fetch the current block author id, if defined.
	fn block_author() -> Option<Self::ReporterId> {
		None
	}
}
