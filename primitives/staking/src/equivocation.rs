use crate::offence::{Offence, OffenceError};
use sp_core::Get;
use sp_runtime::DispatchResult;

pub trait EquivocationHandler2 {
	/// The longevity, in blocks, that the equivocation report is valid for. When using the staking
	/// pallet this should be equal to the bonding duration (in blocks, not eras).
	type ReportLongevity: Get<u64>;

	type AccountId;

	type Offence: Offence<Self::KeyOwnerIdentification>;

	type KeyOwnerIdentification;

	type EquivocationProof;

	type KeyOwnerProof;

	/// Report an offence proved by the given reporters.
	fn report_offence(
		reporters: Vec<Self::AccountId>,
		offence: Self::Offence,
	) -> Result<(), OffenceError>;

	/// Returns true if all of the offenders at the given time slot have already been reported.
	fn is_known_offence(
		offenders: &[Self::KeyOwnerIdentification],
		time_slot: &<Self::Offence as Offence<Self::KeyOwnerIdentification>>::TimeSlot,
	) -> bool;

	/// Create and dispatch an equivocation report extrinsic.
	fn submit_unsigned_equivocation_report(
		equivocation_proof: Self::EquivocationProof,
		key_owner_proof: Self::KeyOwnerProof,
	) -> DispatchResult;

	/// Fetch the current block author id, if defined.
	fn block_author() -> Option<Self::AccountId>;
}

// impl<T> HandleEquivocation2 for () {
// 	type ReportLongevity = ();
// 	type AccountId = ();

// 	fn report_offence(
// 		_reporters: Vec<T::AccountId>,
// 		_offence: BabeEquivocationOffence<T::KeyOwnerIdentification>,
// 	) -> Result<(), OffenceError> {
// 		Ok(())
// 	}

// 	fn is_known_offence(_offenders: &[T::KeyOwnerIdentification], _time_slot: &Slot) -> bool {
// 		true
// 	}

// 	fn submit_unsigned_equivocation_report(
// 		_equivocation_proof: EquivocationProof<T::Header>,
// 		_key_owner_proof: T::KeyOwnerProof,
// 	) -> DispatchResult {
// 		Ok(())
// 	}

// 	fn block_author() -> Option<T::AccountId> {
// 		None
// 	}
// }
