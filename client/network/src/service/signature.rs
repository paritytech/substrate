use super::*;

/// A result of signing a message with a network identity. Since `PeerId` is potentially a hash of a
/// `PublicKey`, you need to reveal the `PublicKey` next to the signature, so the verifier can check
/// if the signature was made by the entity that controls a given `PeerId`.
pub struct Signature {
	/// The public key derived from the network identity that signed the message.
	pub public_key: PublicKey,
	/// The actual signature made for the message signed.
	pub bytes: Vec<u8>,
}

impl Signature {
	/// Create a signature for a message with a given network identity.
	pub fn sign_message(
		message: impl AsRef<[u8]>,
		keypair: &Keypair,
	) -> Result<Self, SigningError> {
		let public_key = keypair.public();
		let bytes = keypair.sign(message.as_ref())?;
		Ok(Self { public_key, bytes })
	}

	/// Verify whether the signature was made for the given message by the entity that controls the
	/// given `PeerId`.
	pub fn verify(&self, message: impl AsRef<[u8]>, peer_id: &PeerId) -> bool {
		*peer_id == self.public_key.to_peer_id() &&
			self.public_key.verify(message.as_ref(), &self.bytes)
	}
}
