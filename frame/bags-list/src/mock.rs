use super::*;
use frame_election_provider_support::VoteWeight;
use frame_support::parameter_types;

pub type AccountId = u32;
pub type Balance = u32;

parameter_types! {
	pub static NextVoteWeight: VoteWeight = 0;
}

pub struct StakingMock;
impl frame_election_provider_support::VoteWeightProvider<AccountId> for StakingMock {
	fn vote_weight(_: &AccountId) -> VoteWeight {
		NextVoteWeight::get()
	}
	#[cfg(any(feature = "runtime-benchmarks", test))]
	fn set_vote_weight_of(_: &AccountId, weight: VoteWeight) {
		// we don't really keep a mapping, just set weight for everyone.
		NextVoteWeight::set(weight)
	}
}

impl frame_system::Config for Runtime {
	type SS58Prefix = ();
	type BaseCallFilter = frame_support::traits::AllowAll;
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = Call;
	type Hash = sp_core::H256;
	type Hashing = sp_runtime::traits::BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = sp_runtime::traits::IdentityLookup<Self::AccountId>;
	type Header = sp_runtime::testing::Header;
	type Event = Event;
	type BlockHashCount = ();
	type DbWeight = ();
	type BlockLength = ();
	type BlockWeights = ();
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<Balance>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type OnSetCode = ();
}

/// Thresholds used for bags.
const THRESHOLDS: [VoteWeight; 9] = [10, 20, 30, 40, 50, 60, 1_000, 2_000, 10_000];

parameter_types! {
	pub static BagThresholds: &'static [VoteWeight] = &THRESHOLDS;
}

impl crate::Config for Runtime {
	type Event = Event;
	type WeightInfo = ();
	type BagThresholds = BagThresholds;
	type VoteWeightProvider = StakingMock;
}

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Runtime>;
type Block = frame_system::mocking::MockBlock<Runtime>;
frame_support::construct_runtime!(
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Storage, Event<T>, Config},
		BagsList: crate::{Pallet, Call, Storage, Event<T>},
	}
);

pub(crate) mod ext_builder {
	use super::*;

	/// Default AccountIds and their weights.
	const GENESIS_IDS: [(AccountId, VoteWeight); 4] = [(1, 10), (2, 1_000), (3, 1_000), (4, 1_000)];

	#[derive(Default)]
	pub(crate) struct ExtBuilder {
		ids: Vec<(AccountId, VoteWeight)>,
	}

	impl ExtBuilder {
		/// Add some AccountIds to insert into `List`.
		pub(crate) fn add_ids(mut self, ids: Vec<(AccountId, VoteWeight)>) -> Self {
			self.ids = ids;
			self
		}

		pub(crate) fn build(self) -> sp_io::TestExternalities {
			sp_tracing::try_init_simple();
			let storage =
				frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();

			let mut ext = sp_io::TestExternalities::from(storage);
			ext.execute_with(|| {
				for (id, weight) in GENESIS_IDS.iter().chain(self.ids.iter()) {
					frame_support::assert_ok!(
						List::<Runtime>::insert(*id, *weight)
					);
				}
			});

			ext
		}

		pub(crate) fn build_and_execute(self, test: impl FnOnce() -> ()) {
			self.build().execute_with(|| {
				test();
				List::<Runtime>::sanity_check().expect("Sanity check post condition failed")
			})
		}

		pub(crate) fn build_and_execute_no_post_check(self, test: impl FnOnce() -> ()) {
			self.build().execute_with(test)
		}
	}
}

pub(crate) mod test_utils {
	use super::*;
	use list::Bag;

	/// Returns the nodes of all non-empty bags.
	pub(crate) fn get_bags() -> Vec<(VoteWeight, Vec<AccountId>)> {
		BagThresholds::get()
			.into_iter()
			.chain(std::iter::once(&VoteWeight::MAX)) // assumes this is not an explicit threshold
			.filter_map(|t| {
				Bag::<Runtime>::get(*t)
					.map(|bag| (*t, bag.iter().map(|n| n.id().clone()).collect::<Vec<_>>()))
			})
			.collect::<Vec<_>>()
	}

	pub(crate) fn bag_as_ids(bag: &Bag<Runtime>) -> Vec<AccountId> {
		bag.iter().map(|n| *n.id()).collect::<Vec<_>>()
	}

	pub(crate) fn get_list_as_ids() -> Vec<AccountId> {
		List::<Runtime>::iter().map(|n| *n.id()).collect::<Vec<_>>()
	}

	pub(crate) fn set_bag_thresholds(thresholds: &'static [VoteWeight]) {
		BagThresholds::set(thresholds);
	}
}
