use crate::{offence::Offence, SessionIndex};
use sp_core::Get;
use sp_runtime::{DispatchResult, Perbill};
use sp_std::vec::Vec;

/// TODO:<<<<<<<<<<<< BETTER DOCS
///
/// A system capable of construct, report and submit offences.
///
/// Implementors of this trait provides a wrapper around the lower level rough
/// system in order to provide exitrinsic submission of reports an construction
/// of offences given the offence and offender key ownership proofs.
///
/// It is assumed that this subsystem takes care of checking key ownership proof
/// before report submission.
pub trait OffenceReportSystem {
	/// TODO: DOC
	type Offence: Offence;

	/// TODO: DOC
	type OffenceProof;

	/// TODO: DOC
	type KeyOwnerProof;

	/// Longevity, in blocks, for the report validity. When using the staking
	/// pallet this should be equal to the bonding duration (in blocks, not eras).
	type ReportLongevity: Get<u64>;

	/// Offence reporter type
	type Reporter;

	/// Report offence to the `ReportOffence` handler.
	fn report_evidence(
		_reporter: Option<Self::Reporter>,
		_offence_proof: Self::OffenceProof,
		_key_owner_proof: Self::KeyOwnerProof,
	) -> DispatchResult {
		Ok(())
	}

	/// Check if is a known offence.
	fn check_evidence(
		_offence_proof: &Self::OffenceProof,
		_key_owner_proof: &Self::KeyOwnerProof,
	) -> DispatchResult {
		Ok(())
	}

	/// Create and dispatch an offence report extrinsic.
	fn submit_evidence(
		_offence_proof: Self::OffenceProof,
		_key_owner_proof: Self::KeyOwnerProof,
	) -> bool {
		true
	}
}

// Dummy offence type meant to be used by the dummy offence report system.
impl Offence for () {
	const ID: crate::offence::Kind = [0; 16];
	type TimeSlot = ();
	type Offender = ();

	fn offenders(&self) -> Vec<Self::Offender> {
		Default::default()
	}

	fn validator_set_count(&self) -> u32 {
		0
	}

	fn time_slot(&self) -> Self::TimeSlot {
		()
	}

	fn session_index(&self) -> SessionIndex {
		0
	}

	fn slash_fraction(&self, _offenders_count: u32) -> Perbill {
		Default::default()
	}
}

// Dummy report system.
// Should always give successful results
impl OffenceReportSystem for () {
	type Offence = ();

	type Reporter = ();

	type OffenceProof = ();

	type KeyOwnerProof = ();

	type ReportLongevity = ();
}
