use super::*;

pub(super) const PREFIX: &[u8] = b"historical";
pub(super) const LAST_PRUNE: &[u8] = b"historical_last_prune";

/// Derive the key used to store the list of validators
pub(super) fn derive_key<P: AsRef<[u8]>>(prefix: P, session_index: SessionIndex) -> Vec<u8> {
    let prefix: &[u8] = prefix.as_ref();
    let encoded_session_index = session_index.encode();
    assert!(encoded_session_index.len() > 0);
    let mut concatenated = Vec::with_capacity(prefix.len() + 1 + encoded_session_index.len());
    concatenated.extend_from_slice(prefix);
    concatenated.push('/' as u8);
    concatenated.extend_from_slice(encoded_session_index.as_slice());
    concatenated
}