use crate::offence::{Offence, OffenceError, ReportOffence};
use sp_core::Get;
use sp_runtime::DispatchResult;

pub trait EquivocationHandler {
	type Offence: Offence;

	type OffenceProof;

	type KeyOwnerProof;

	type ReportOffence: ReportOffence<Self::Offence>;

	/// The longevity, in blocks, that the equivocation report is valid for. When using the staking
	/// pallet this should be equal to the bonding duration (in blocks, not eras).
	type ReportLongevity: Get<u64>;

	fn report_offence(offence: Self::Offence) -> Result<(), OffenceError> {
		Self::ReportOffence::report_offence(offence)
	}

	fn is_known_offence(
		offenders: &[<Self::Offence as Offence>::Offender],
		time_slot: &<Self::Offence as Offence>::TimeSlot,
	) -> bool {
		Self::ReportOffence::is_known_offence(offenders, time_slot)
	}

	/// Create and dispatch an offence report extrinsic.
	fn submit_offence_proof(
		_offence_proof: Self::OffenceProof,
		_key_owner_proof: Self::KeyOwnerProof,
	) -> DispatchResult {
		Ok(())
	}

	/// Fetch the current reporter id, if defined.
	// TODO: rename to reporter and move to offence trait?
	fn block_author() -> Option<<Self::Offence as Offence>::Reporter> {
		None
	}
}
