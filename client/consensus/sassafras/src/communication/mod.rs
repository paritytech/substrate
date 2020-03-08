mod network;

use futures::channel::mpsc::{UnboundedSender, UnboundedReceiver};
use sp_consensus_sassafras::{SlotNumber, VRFProof};
use crate::PublishingSet;

pub use self::network::{
	SASSAFRAS_ENGINE_ID, SASSAFRAS_PROTOCOL_NAME, GossipValidator, NetworkBridge,
};

pub fn send_out(
	sender: &UnboundedSender<VRFProof>,
	slot_number: SlotNumber,
	set: &mut PublishingSet
) {
	const SEND_OUT_LIMIT: usize = 4;

	let mut sent = 0;
	for pending in &mut set.pending {
		if sent >= SEND_OUT_LIMIT {
			return
		}

		if pending.submit_status.is_none() {
			match sender.unbounded_send(pending.vrf_proof.clone()) {
				Ok(()) => {
					pending.submit_status = Some(slot_number);
				},
				Err(_) => return,
			}
		}
	}
}

pub fn receive_in(
	receiver: &mut UnboundedReceiver<VRFProof>,
	set: &mut PublishingSet,
) {
	while let Ok(Some(proof)) = receiver.try_next() {
		set.disclosing.push(proof);
	}
}
