#![cfg_attr(not(feature = "std"), no_std)]
#![allow(clippy::too_many_arguments)]

sp_api::decl_runtime_apis! {
	pub trait ImOnlineApi {
		fn is_online(authority_index: u32) -> bool;
	}
}
