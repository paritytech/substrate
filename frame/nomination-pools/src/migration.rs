use super::*;

pub mod v1 {
	use super::*;
	use crate::log;
	use frame_support::traits::OnRuntimeUpgrade;

	#[derive(Decode)]
	pub struct OldPoolRoles<AccountId> {
		pub depositor: AccountId,
		pub root: AccountId,
		pub nominator: AccountId,
		pub state_toggler: AccountId,
	}

	impl<AccountId> OldPoolRoles<AccountId> {
		fn migrate_to_v1(self) -> PoolRoles<AccountId> {
			PoolRoles {
				depositor: self.depositor,
				root: Some(self.root),
				nominator: Some(self.nominator),
				state_toggler: Some(self.state_toggler),
			}
		}
	}

	#[derive(Decode)]
	pub struct OldBondedPoolInner<T: Config> {
		pub points: BalanceOf<T>,
		pub state: PoolState,
		pub member_counter: u32,
		pub roles: OldPoolRoles<T::AccountId>,
	}

	impl<T: Config> OldBondedPoolInner<T> {
		fn migrate_to_v1(self) -> BondedPoolInner<T> {
			BondedPoolInner {
				member_counter: self.member_counter,
				points: self.points,
				state: self.state,
				roles: self.roles.migrate_to_v1(),
			}
		}
	}

	pub struct MigrateToV1<T>(sp_std::marker::PhantomData<T>);
	impl<T: Config> OnRuntimeUpgrade for MigrateToV1<T> {
		fn on_runtime_upgrade() -> Weight {
			let current = Pallet::<T>::current_storage_version();
			let onchain = Pallet::<T>::on_chain_storage_version();

			log!(
				info,
				"Running migration with current storage version {:?} / onchain {:?}",
				current,
				onchain
			);

			if current == 1 && onchain == 0 {
				// this is safe to execute on any runtime that has a bounded number of pools.
				let mut translated = 0u64;
				BondedPools::<T>::translate::<OldBondedPoolInner<T>, _>(|_key, old_value| {
					translated.saturating_inc();
					Some(old_value.migrate_to_v1())
				});
				current.put::<Pallet<T>>();

				T::DbWeight::get().reads_writes(translated, translated)
			} else {
				log!(info, "Migration did not executed. This probably should be removed");
				T::DbWeight::get().reads(1)
			}
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade() -> Result<(), &'static str> {}
	}
}
