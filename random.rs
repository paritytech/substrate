// stuff for the P2 staking
/* /Users/romanuseinov/projects/parity/substrate/frame/staking/src/lib.rs
/// An unbounded version of `Nominations`, use for some really wacky hacks.
#[derive(PartialEqNoBound, EqNoBound, Clone, Encode, Decode, RuntimeDebugNoBound, TypeInfo)]
#[codec(mel_bound())]
#[scale_info(skip_type_params(T))]
struct UnboundedNominations<T: Config> {
	pub targets: Vec<T::AccountId>,
	pub submitted_in: EraIndex,
	pub suppressed: bool,
}

/Users/romanuseinov/projects/parity/substrate/bin/node/runtime/src/lib.rs
		TargetBagsList: pallet_bags_list::<Instance2>,

type TargetBagsListInstance = pallet_bags_list::Instance2;
impl pallet_bags_list::Config<TargetBagsListInstance> for Runtime {
	type Event = Event;
	// The bags-list itself will be the source of truth about the approval stakes. This implies that
	// staking should keep the approval stakes up to date at all times.
	type ScoreProvider = TargetBagsList;
	type BagThresholds = BagThresholdsBalance;
	type Score = Balance;
	type WeightInfo = pallet_bags_list::weights::SubstrateWeight<Runtime>;
}
bin/node/runtime/src/lib.rs
	// This parameter is going to be needed for the operational TargetList implementation
	pub const BagThresholdsBalance: &'static [u128] = &voter_bags::THRESHOLDS_BALANCES;

/Users/romanuseinov/projects/parity/substrate/frame/staking/src/mock.rs
		TargetBagsList: pallet_bags_list::<Instance2>::{Pallet, Call, Storage, Event<T>},

type TargetBagsListInstance = pallet_bags_list::Instance2;
impl pallet_bags_list::Config<TargetBagsListInstance> for Test {
	type Event = Event;
	type WeightInfo = ();
	// Target bags-list are always kept up to date, and in fact Staking does not know them at all!
	type ScoreProvider = pallet_bags_list::Pallet<Self, TargetBagsListInstance>;
	type BagThresholds = BagThresholdsBalance;
	type Score = Balance;
}

pub struct TargetBagsListCompat;
impl SortedListProvider<AccountId> for TargetBagsListCompat {
	type Error = <TargetBagsList as SortedListProvider<AccountId>>::Error;
	type Score = <TargetBagsList as SortedListProvider<AccountId>>::Score;

	fn iter() -> Box<dyn Iterator<Item = AccountId>> {
		let mut all = TargetBagsList::iter()
			.map(|x| (x, TargetBagsList::get_score(&x).unwrap_or_default()))
			.collect::<Vec<_>>();
		all.sort_by(|a, b| match a.1.partial_cmp(&b.1).unwrap() {
			std::cmp::Ordering::Equal => b.0.partial_cmp(&a.0).unwrap(),
			// Question: why rerverse?
			x @ _ => x.reverse(),
		});
		Box::new(all.into_iter().map(|(x, _)| x))
	}
	fn iter_from(start: &AccountId) -> Result<Box<dyn Iterator<Item = AccountId>>, Self::Error> {
		TargetBagsList::iter_from(start)
	}
	fn count() -> u32 {
		TargetBagsList::count()
	}
	fn contains(id: &AccountId) -> bool {
		TargetBagsList::contains(id)
	}
	fn on_insert(id: AccountId, weight: Self::Score) -> Result<(), Self::Error> {
		TargetBagsList::on_insert(id, weight)
	}
	fn on_update(id: &AccountId, weight: Self::Score) -> Result<(), Self::Error> {
		TargetBagsList::on_update(id, weight)
	}
	fn get_score(id: &AccountId) -> Result<Self::Score, Self::Error> {
		TargetBagsList::get_score(id)
	}
	fn on_remove(id: &AccountId) -> Result<(), Self::Error> {
		TargetBagsList::on_remove(id)
	}
	fn unsafe_regenerate(
		all: impl IntoIterator<Item = AccountId>,
		weight_of: Box<dyn Fn(&AccountId) -> Self::Score>,
	) -> u32 {
		TargetBagsList::unsafe_regenerate(all, weight_of)
	}
	fn unsafe_clear() {
		TargetBagsList::unsafe_clear();
	}
	fn sanity_check() -> Result<(), &'static str> {
		TargetBagsList::sanity_check()
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn score_update_worst_case(_who: &AccountId, _is_increase: bool) -> Self::Score {
		Balance::MAX
	}
}

frame/staking/src/mock.rs
	const THRESHOLDS_BALANCE: [Balance; 9] = [10, 20, 30, 40, 50, 60, 1_000, 2_000, 10_000];

	pub static BagThresholdsBalance: &'static [sp_npos_elections::ExtendedBalance] = &THRESHOLDS_BALANCE;

 */
