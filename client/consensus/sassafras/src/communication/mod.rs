mod network;

use aead::Aead;
use codec::{Encode, Decode};
use futures::channel::mpsc::{UnboundedSender, UnboundedReceiver};
use sp_consensus_sassafras::{SlotNumber, AuthorityId, AuthorityPair};
use sp_consensus_vrf::schnorrkel::VRFOutput;
use sc_keystore::KeyStorePtr;
use log::trace;
use crate::PublishingSet;

pub use self::network::{
	SASSAFRAS_ENGINE_ID, SASSAFRAS_PROTOCOL_NAME, GossipValidator, NetworkBridge,
};

mod cost {
	use sc_network::ReputationChange as Rep;
}

mod benefit {
	use sc_network::ReputationChange as Rep;
}

pub fn send_out(
	sender: &UnboundedSender<(AuthorityId, [u8; 32], Vec<u8>)>,
	set: &mut PublishingSet,
	slot_number: SlotNumber,
) {
	const SEND_OUT_LIMIT: usize = 4;

	let mut sent = 0;
	for pending in &mut set.pending {
		if sent >= SEND_OUT_LIMIT {
			return
		}

		if pending.submit_status.is_none() {
			if set.outputs.contains(&pending.vrf_output) ||
				set.disclosing.contains(&pending.vrf_output)
			{
				pending.submit_status = Some(slot_number);
				continue
			}

			let receiver_id = set.authorities[pending.submit_authority_index as usize].0.clone();
			let receiver_public = match schnorrkel::PublicKey::from_bytes(receiver_id.as_ref()) {
				Ok(public) => public,
				Err(_) => {
					trace!(
						target: "sassafras_communication",
						"Sending out a pending message, but receiver id decoding failed, ignoring",
					);
					continue
				},
			};
			let (ephemeral_key, aead) = receiver_public
				.init_aead32_unauthenticated::<aes_gcm::Aes256Gcm>();
			let encrypted = match aead.encrypt(
				&Default::default(),
				&pending.vrf_output.encode()[..],
			) {
				Ok(encrypted) => encrypted,
				Err(_) => {
					trace!(
						target: "sassafras_communication",
						"Sending out a pending message, but encrypting it failed, ignoring",
					);
					continue
				},
			};

			match sender.unbounded_send((receiver_id, ephemeral_key.to_bytes(), encrypted)) {
				Ok(()) => {
					trace!(
						target: "sassafras_communication",
						"Successfully sent out a pending message.",
					);
					pending.submit_status = Some(slot_number);
				},
				Err(_) => {
					trace!(
						target: "sassafras_communication",
						"Sending out a pending message, but the channel signaled failure, breaking",
					);
					break
				},
			}
		}
	}
}

pub fn receive_in(
	receiver: &mut UnboundedReceiver<(AuthorityId, [u8; 32], Vec<u8>)>,
	set: &mut PublishingSet,
	keystore: &KeyStorePtr,
) {
	let keystore = keystore.read();

	while let Ok(Some((receiver_id, ephemeral_key, encrypted))) = receiver.try_next() {
		let receiver_pair = match keystore.key_pair::<AuthorityPair>(&receiver_id) {
			Ok(pair) => pair,
			Err(_) => {
				trace!(
					target: "sassafras_communication",
					"Received an encypted message, but the key pair cannot be found, ignoring."
				);
				continue
			},
		};
		let pair = crate::authorship::get_keypair(&receiver_pair);
		let aead = pair.secret.aead32_unauthenticated::<aes_gcm::Aes256Gcm>(
			&match schnorrkel::PublicKey::from_bytes(&ephemeral_key) {
				Ok(key) => key,
				Err(_) => {
					trace!(
						target: "sassafras_communication",
						"Received an encrypted message, but the public key decoding failed, ignoring."
					);
					continue
				},
			}
		);
		let decrypted = match aead.decrypt(
			&Default::default(),
			&encrypted[..],
		) {
			Ok(decrypted) => decrypted,
			Err(_) => {
				trace!(
					target: "sassafras_communication",
					"Received an ecrypted message, but decrypting it failed, ignoring."
				);
				continue
			},
		};
		let output = match VRFOutput::decode(&mut &decrypted[..]) {
			Ok(output) => output,
			Err(_) => {
				trace!(
					target: "sassafras_communication",
					"Received an encrypted message, but the proof decoding failed, ignoring."
				);
				continue
			},
		};

		if set.outputs.contains(&output) || set.disclosing.contains(&output) {
			continue
		}

		trace!(
			target: "sassafras_communication",
			"Received an encrypted message and decoded it as output {:?}", output
		);
		set.disclosing.push(output);
	}
}
