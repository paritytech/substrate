/// Compute the existential weight for the specified configuration.
///
/// Note that this value depends on the current issuance, a quantity known to change over time.
/// This makes the project of computing a static value suitable for inclusion in a static,
/// generated file _excitingly unstable_.
#[cfg(any(feature = "std", feature = "make-bags"))]
pub fn existential_weight<T: Config>() -> VoteWeight {
	// use frame_support::traits::{Currency, CurrencyToVote};

	let existential_deposit = <T::Currency as Currency<T::AccountId>>::minimum_balance();
	let issuance = <T::Currency as Currency<T::AccountId>>::total_issuance();
	T::CurrencyToVote::to_vote(existential_deposit, issuance)
}
