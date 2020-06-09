use codec::Encode;
use sp_runtime::traits::Convert;

use super::super::Trait as SessionTrait;
use super::super::{Module as SessionModule, SessionIndex};
use super::Trait as HistoricalTrait;

use super::shared;

/// Store the validator set associated to the `session_index` to the off-chain database.
///
/// **Must** be called from on-chain, i.e. `on_initialize(..)` or `on_finalization(..)`.
pub fn store_session_validator_set_to_offchain<T: HistoricalTrait + SessionTrait>(
	session_index: SessionIndex,
) {
	//let value = SessionModule::historical_root(session_index);
	let encoded_validator_list = <SessionModule<T>>::validators()
		.into_iter()
		.filter_map(|validator_id: <T as SessionTrait>::ValidatorId| {
			let full_identification =
				<<T as HistoricalTrait>::FullIdentificationOf>::convert(validator_id.clone());
			full_identification.map(|full_identification| (validator_id, full_identification))
		})
		.collect::<Vec<_>>();

	encoded_validator_list.using_encoded(|encoded_validator_list| {
		let derived_key = shared::derive_key(shared::PREFIX, session_index);
		sp_io::offchain_index::set(derived_key.as_slice(), encoded_validator_list);
	});
}

/// Store the validator set associated to the _current_ session index to the off-chain database.
///
/// **Must** be called from on-chain, i.e. `on_initialize(..)` or `on_finalization(..)`.
pub fn store_current_session_validator_set_to_offchain<T: HistoricalTrait + SessionTrait>() {
	store_session_validator_set_to_offchain::<T>(<SessionModule<T>>::current_index());
}
