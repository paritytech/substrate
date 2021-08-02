use codec::{Decode, Encode};
use sp_runtime::traits::Block as BlockT;
use sp_runtime::AccountId32;

/// Information about extrinsic fetched from runtime API
#[derive(Encode, Decode, PartialEq)]
pub struct ExtrinsicInfo {
	/// extrinsic signer
	pub who: AccountId32,
	/// nonce
	pub nonce: u32,
}

sp_api::decl_runtime_apis! {
	/// The `ExtrinsicInfoRuntimeApi` api trait for fetching information about extrinsic author and
	/// nonce
	pub trait ExtrinsicInfoRuntimeApi {

		/// Provides information about extrinsic signer and nonce
		fn get_info(
			tx: <Block as BlockT>::Extrinsic,
		) -> Option<ExtrinsicInfo>;
	}
}
