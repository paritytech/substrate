use schnorrkel::vrf::VRFProof;
use sp_core::H256;
use sp_consensus_sassafras::{SlotNumber, SassafrasBlockWeight};
use sp_blockchain::Result as ClientResult;
use sc_client_api::AuxStore;

pub struct PublishingAuxiliary {
	pub proofs: Vec<VRFProof>,
	pub start_slot: SlotNumber,
}

pub struct GeneratingAuxiliary {
	pub proofs: Vec<VRFProof>,
	pub start_slot: SlotNumber,
}

pub struct Auxiliary {
	pub total_weight: SassafrasBlockWeight,
	pub weight: SassafrasBlockWeight,

	pub publishing: PublishingAuxiliary,
	pub validating: GeneratingAuxiliary,
}

pub(crate) fn read_auxiliary<B: AuxStore>(
	hash: &H256,
	backend: &B
) -> ClientResult<Auxiliary> {
	unimplemented!()
}

pub(crate) fn write_auxiliary<B: AuxStore>(
	auxiliary: &Auxiliary,
	backend: &B
) -> ClientResult<()> {
	unimplemented!()
}
