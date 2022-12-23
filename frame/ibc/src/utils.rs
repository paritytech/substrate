use crate::Config;
use scale_info::prelude::format;

/// Get the latest block height of the host chain
pub fn host_height<T: Config>() -> u64 {
	let block_number = format!("{:?}", <frame_system::Pallet<T>>::block_number());
	let current_height: u64 = block_number.parse().unwrap_or_default();
	current_height
}
