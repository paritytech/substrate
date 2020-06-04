
use codec::Encode;

use super::super::{Module as SessionModule, SessionIndex};
use super::Trait;

use super::shared;

/// Store the validator set associated to the `session_index` to the off-chain database.
///
/// **Must** be called from on-chain, i.e. `on_initialize(..)` or `on_finalization(..)`.
pub fn store_session_validator_set_to_offchain<T: Trait>(session_index: SessionIndex) {
	let derived_key = shared::derive_key(shared::PREFIX, session_index);
	//let value = SessionModule::historical_root(session_index);
	let encoded_validator_list = <SessionModule<T>>::validators().encode();
	sp_io::offchain_index::set(derived_key.as_slice(), encoded_validator_list.as_slice())
}

/// Store the validator set associated to the _current_ session index to the off-chain database.
///
/// **Must** be called from on-chain, i.e. `on_initialize(..)` or `on_finalization(..)`.
pub fn store_current_session_validator_set_to_offchain<T: Trait>() {
	store_session_validator_set_to_offchain::<T>(<SessionModule<T>>::current_index());
}