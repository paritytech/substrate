#![cfg(feature = "runtime-benchmarks")]

use frame_support::benchmarks;

#[benchmarks]
mod benchmarks {
	use super::super::*;

	use frame_system::RawOrigin;
	//use sp_runtime::traits::Bounded;

	use crate::Pallet as Balances;

	const SEED: u32 = 0;
	// existential deposit multiplier
	const ED_MULTIPLIER: u32 = 10;

	use frame_benchmarking::{account, whitelisted_caller};
	use frame_support::{instance_benchmark, Linear};

	#[instance_benchmark]
	fn transfer() {
		let existential_deposit = T::ExistentialDeposit::get();
		let caller = whitelisted_caller();

		// Give some multiple of the existential deposit
		let balance = existential_deposit.saturating_mul(ED_MULTIPLIER.into());
		let _ = <Balances<T, I> as Currency<_>>::make_free_balance_be(&caller, balance);

		// Transfer `e - 1` existential deposits + 1 unit, which guarantees to create one account,
		// and reap this user.
		let recipient: T::AccountId = account("recipient", 0, SEED);
		let recipient_lookup = T::Lookup::unlookup(recipient.clone());
		let transfer_amount =
			existential_deposit.saturating_mul((ED_MULTIPLIER - 1).into()) + 1u32.into();

		#[extrinsic_call]
		transfer(RawOrigin::Signed(caller.clone()), recipient_lookup, transfer_amount);

		assert_eq!(Balances::<T, I>::free_balance(&caller), Zero::zero());
		assert_eq!(Balances::<T, I>::free_balance(&recipient), transfer_amount);
	}
}
