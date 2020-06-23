use frame_support::weights::{Weight, constants::RocksDbWeight};
use pallet_balances::BalancesWeight;
pub struct WeightForBalances;
impl BalancesWeight for WeightForBalances {
	fn transfer(u: u32, e: u32, ) -> Weight {
		(574875000 as Weight)
			.saturating_add((u as Weight).saturating_mul(7000 as Weight))
			.saturating_add((e as Weight).saturating_mul(0 as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((u as Weight).saturating_mul(0 as Weight)))
			.saturating_add(RocksDbWeight::get().reads((e as Weight).saturating_mul(0 as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((u as Weight).saturating_mul(0 as Weight)))
			.saturating_add(RocksDbWeight::get().writes((e as Weight).saturating_mul(0 as Weight)))
	}
	fn transfer_best_case(u: u32, e: u32, ) -> Weight {
		(368265000 as Weight)
			.saturating_add((u as Weight).saturating_mul(26000 as Weight))
			.saturating_add((e as Weight).saturating_mul(0 as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((u as Weight).saturating_mul(0 as Weight)))
			.saturating_add(RocksDbWeight::get().reads((e as Weight).saturating_mul(0 as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((u as Weight).saturating_mul(0 as Weight)))
			.saturating_add(RocksDbWeight::get().writes((e as Weight).saturating_mul(0 as Weight)))
	}
	fn transfer_keep_alive(u: u32, e: u32, ) -> Weight {
		(402076000 as Weight)
			.saturating_add((u as Weight).saturating_mul(7000 as Weight))
			.saturating_add((e as Weight).saturating_mul(14000 as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((u as Weight).saturating_mul(0 as Weight)))
			.saturating_add(RocksDbWeight::get().reads((e as Weight).saturating_mul(0 as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((u as Weight).saturating_mul(0 as Weight)))
			.saturating_add(RocksDbWeight::get().writes((e as Weight).saturating_mul(0 as Weight)))
	}
	fn set_balance(u: u32, e: u32, ) -> Weight {
		(341092000 as Weight)
			.saturating_add((u as Weight).saturating_mul(0 as Weight))
			.saturating_add((e as Weight).saturating_mul(12000 as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((u as Weight).saturating_mul(0 as Weight)))
			.saturating_add(RocksDbWeight::get().reads((e as Weight).saturating_mul(0 as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((u as Weight).saturating_mul(0 as Weight)))
			.saturating_add(RocksDbWeight::get().writes((e as Weight).saturating_mul(0 as Weight)))
	}
	fn set_balance_killing(u: u32, e: u32, ) -> Weight {
		(412116000 as Weight)
			.saturating_add((u as Weight).saturating_mul(28000 as Weight))
			.saturating_add((e as Weight).saturating_mul(0 as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((u as Weight).saturating_mul(0 as Weight)))
			.saturating_add(RocksDbWeight::get().reads((e as Weight).saturating_mul(0 as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((u as Weight).saturating_mul(0 as Weight)))
			.saturating_add(RocksDbWeight::get().writes((e as Weight).saturating_mul(0 as Weight)))
	}
}
