use srml_support::{StorageValue, decl_storage, decl_module};
use srml_support::traits::Get;
use pow_primitives::Difficulty;
use sr_primitives::traits::{UniqueSaturatedInto, Zero};

pub trait Trait: timestamp::Trait {
	type Span: Get<Self::BlockNumber>;
	type TargetPeriod: Get<Self::Moment>;
	type InitialDifficulty: Get<Difficulty>;
}

decl_storage! {
	trait Store for Module<T: Trait> as AverageSpanDifficultyAdjustment {
		LastTimestamp get(last_timestamp): Option<T::Moment>;
		TargetDifficulty get(target_difficulty)
			build(|_| <T::InitialDifficulty>::get()): Difficulty;
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn on_finalize(n: T::BlockNumber) {
			if n % <T::Span>::get() == Zero::zero() {
				if let Some(last_timestamp) = Self::last_timestamp() {
					let current_timestamp = <timestamp::Module<T>>::now();
					if current_timestamp <= last_timestamp {
						return
					}

					let accumulated_difficulty = Self::target_difficulty() *
						<T::Span>::get().unique_saturated_into();

					let target_difficulty = accumulated_difficulty *
						<T::TargetPeriod>::get().unique_saturated_into() /
						(current_timestamp - last_timestamp).unique_saturated_into();
					<TargetDifficulty>::put(target_difficulty);
				}

				<LastTimestamp<T>>::put(<timestamp::Module<T>>::now());
			}
		}
	}
}
