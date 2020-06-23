use frame_support::weights::Weight;
use frame_support::traits::Get;

use pallet_balances::BalancesWeight;

pub struct WeightForBalances;

impl<T: frame_system::Trait> BalancesWeight<T> for WeightForBalances {
	fn balances_transfer(u: u32, e: u32, ) -> Weight {
		(998433000 as Weight)
			.saturating_add((u as Weight).saturating_mul(0 as Weight))
			.saturating_add((e as Weight).saturating_mul(0 as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().reads((u as Weight).saturating_mul(0 as Weight)))
			.saturating_add(T::DbWeight::get().reads((e as Weight).saturating_mul(0 as Weight)))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			.saturating_add(T::DbWeight::get().writes((u as Weight).saturating_mul(0 as Weight)))
			.saturating_add(T::DbWeight::get().writes((e as Weight).saturating_mul(0 as Weight)))
	}
	fn balances_transfer_best_case(u: u32, e: u32, ) -> Weight {
		(553917000 as Weight)
			.saturating_add((u as Weight).saturating_mul(0 as Weight))
			.saturating_add((e as Weight).saturating_mul(0 as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().reads((u as Weight).saturating_mul(0 as Weight)))
			.saturating_add(T::DbWeight::get().reads((e as Weight).saturating_mul(0 as Weight)))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			.saturating_add(T::DbWeight::get().writes((u as Weight).saturating_mul(0 as Weight)))
			.saturating_add(T::DbWeight::get().writes((e as Weight).saturating_mul(0 as Weight)))
	}
	fn balances_transfer_keep_alive(u: u32, e: u32, ) -> Weight {
		(483036000 as Weight)
			.saturating_add((u as Weight).saturating_mul(0 as Weight))
			.saturating_add((e as Weight).saturating_mul(23000 as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().reads((u as Weight).saturating_mul(0 as Weight)))
			.saturating_add(T::DbWeight::get().reads((e as Weight).saturating_mul(0 as Weight)))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			.saturating_add(T::DbWeight::get().writes((u as Weight).saturating_mul(0 as Weight)))
			.saturating_add(T::DbWeight::get().writes((e as Weight).saturating_mul(0 as Weight)))
	}
	fn balances_set_balance(u: u32, e: u32, ) -> Weight {
		(332225000 as Weight)
			.saturating_add((u as Weight).saturating_mul(5000 as Weight))
			.saturating_add((e as Weight).saturating_mul(11000 as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().reads((u as Weight).saturating_mul(0 as Weight)))
			.saturating_add(T::DbWeight::get().reads((e as Weight).saturating_mul(0 as Weight)))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			.saturating_add(T::DbWeight::get().writes((u as Weight).saturating_mul(0 as Weight)))
			.saturating_add(T::DbWeight::get().writes((e as Weight).saturating_mul(0 as Weight)))
	}
	fn balances_set_balance_killing(u: u32, e: u32, ) -> Weight {
		(434352000 as Weight)
			.saturating_add((u as Weight).saturating_mul(0 as Weight))
			.saturating_add((e as Weight).saturating_mul(0 as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().reads((u as Weight).saturating_mul(0 as Weight)))
			.saturating_add(T::DbWeight::get().reads((e as Weight).saturating_mul(0 as Weight)))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			.saturating_add(T::DbWeight::get().writes((u as Weight).saturating_mul(0 as Weight)))
			.saturating_add(T::DbWeight::get().writes((e as Weight).saturating_mul(0 as Weight)))
	}
}
