mod network;

use aead::Aead;
use codec::{Encode, Decode};
use futures::channel::mpsc::{UnboundedSender, UnboundedReceiver};
use sp_consensus_sassafras::{SlotNumber, VRFProof, AuthorityId, AuthorityPair};
use sc_keystore::KeyStorePtr;
use crate::PublishingSet;

pub use self::network::{
	SASSAFRAS_ENGINE_ID, SASSAFRAS_PROTOCOL_NAME, GossipValidator, NetworkBridge,
};

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
			let receiver_id = set.authorities[pending.submit_authority_index as usize].0.clone();
			let receiver_public = match schnorrkel::PublicKey::from_bytes(receiver_id.as_ref()) {
				Ok(public) => public,
				Err(_) => continue,
			};
			let (ephemeral_key, aead) = receiver_public
				.init_aead32_unauthenticated::<aes_gcm::Aes256Gcm>();
			let encrypted = match aead.encrypt(
				&Default::default(),
				&pending.vrf_proof.encode()[..],
			) {
				Ok(encrypted) => encrypted,
				Err(_) => continue,
			};

			match sender.unbounded_send((receiver_id, ephemeral_key.to_bytes(), encrypted)) {
				Ok(()) => {
					pending.submit_status = Some(slot_number);
				},
				Err(_) => break,
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
			Err(_) => continue,
		};
		let pair = crate::authorship::get_keypair(&receiver_pair);
		let aead = pair.secret.aead32_unauthenticated::<aes_gcm::Aes256Gcm>(
			&match schnorrkel::PublicKey::from_bytes(&ephemeral_key) {
				Ok(key) => key,
				Err(_) => continue,
			}
		);
		let decrypted = match aead.decrypt(
			&Default::default(),
			&encrypted[..],
		) {
			Ok(decrypted) => decrypted,
			Err(_) => continue,
		};
		let proof = match VRFProof::decode(&mut &decrypted[..]) {
			Ok(proof) => proof,
			Err(_) => continue,
		};

		set.disclosing.push(proof);
	}
}
