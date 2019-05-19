use primitives::sr25519::{Public, Signature};
use babe_primitives::BABE_ENGINE_ID;
use runtime_primitives::generic::DigestItem;
use std::fmt::Debug;
use parity_codec::{Decode, Encode, Input};
use log::{debug, info, error};
use schnorrkel::{
	vrf::{VRFProof, VRFOutput, VRF_OUTPUT_LENGTH, VRF_PROOF_LENGTH},
	PUBLIC_KEY_LENGTH,
};

/// A BABE pre-digest.  It includes:
///
/// * The public key of the author.
/// * The VRF proof.
/// * The VRF output.
/// * The slot number.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BabePreDigest {
	pub(super) vrf_output: VRFOutput,
	pub(super) proof: VRFProof,
	pub(super) author: Public,
	pub(super) slot_num: u64,
}

/// The prefix used by BABE for its VRF keys.
pub const BABE_VRF_PREFIX: &'static [u8] = b"substrate-babe-vrf";

macro_rules! babe_assert_eq {
	($a: expr, $b: expr) => {
		{
			let ref a = $a;
			let ref b = $b;
			if a != b {
				error!(
					target: "babe",
					"Expected {:?} to equal {:?}, but they were not",
					stringify!($a),
					stringify!($b),
				);
				assert_eq!(a, b);
			}
		}
	};
}

type TmpDecode = (
	[u8; VRF_OUTPUT_LENGTH],
	[u8; VRF_PROOF_LENGTH],
	[u8; PUBLIC_KEY_LENGTH],
	u64,
);

impl Encode for BabePreDigest {
	fn encode(&self) -> Vec<u8> {
		let tmp: TmpDecode = (
			*self.vrf_output.as_bytes(),
			self.proof.to_bytes(),
			self.author.0,
			self.slot_num,
		);
		let encoded = parity_codec::Encode::encode(&tmp);
		if cfg!(any(test, debug_assertions)) {
			debug!(target: "babe", "Checking if encoding was correct");
			let decoded_version = Self::decode(&mut &encoded[..])
				.expect("we just encoded this ourselves, so it is correct; qed");
			babe_assert_eq!(decoded_version.proof, self.proof);
			babe_assert_eq!(decoded_version.vrf_output, self.vrf_output);
			babe_assert_eq!(decoded_version.author, self.author);
			babe_assert_eq!(decoded_version.slot_num, self.slot_num);
			debug!(target: "babe", "Encoding was correct")
		}
		encoded
	}
}

impl Decode for BabePreDigest {
	fn decode<R: Input>(i: &mut R) -> Option<Self> {
		let (output, proof, public_key, slot_num): TmpDecode = Decode::decode(i)?;
		Some(BabePreDigest {
			proof: VRFProof::from_bytes(&proof).ok()?,
			vrf_output: VRFOutput::from_bytes(&output).ok()?,
			author: Public(public_key),
			slot_num,
		})
	}
}

/// A digest item which is usable with BABE consensus.
pub trait CompatibleDigestItem: Sized {
	/// Construct a digest item which contains a BABE pre-digest.
	fn babe_pre_digest(seal: BabePreDigest) -> Self;

	/// If this item is an BABE pre-digest, return it.
	fn as_babe_pre_digest(&self) -> Option<BabePreDigest>;

	/// Construct a digest item which contains a BABE seal.
	fn babe_seal(signature: Signature) -> Self;

	/// If this item is a BABE signature, return the signature.
	fn as_babe_seal(&self) -> Option<&Signature>;
}

impl<Hash: Debug> CompatibleDigestItem for DigestItem<Hash, Public, Signature>
{
	fn babe_pre_digest(digest: BabePreDigest) -> Self {
		DigestItem::PreRuntime(BABE_ENGINE_ID, digest.encode())
	}

	fn as_babe_pre_digest(&self) -> Option<BabePreDigest> {
		match self {
			DigestItem::PreRuntime(BABE_ENGINE_ID, seal) => {
				match Decode::decode(&mut &seal[..]) {
					s @ Some(_) => s,
					s @ None => {
						info!(target: "babe", "Failed to decode {:?}", seal);
						s
					}
				}
			}
			_ => {
				info!(target: "babe", "Invalid consensus: {:?}!", self);
				None
			}
		}
	}

	fn babe_seal(signature: Signature) -> Self {
		DigestItem::Seal(BABE_ENGINE_ID, signature)
	}

	fn as_babe_seal(&self) -> Option<&Signature> {
		match self {
			DigestItem::Seal(BABE_ENGINE_ID, signature) => Some(signature),
			_ => None,
		}
	}
}
