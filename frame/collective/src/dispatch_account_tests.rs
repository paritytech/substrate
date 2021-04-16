use crate::*;
use frame_support::{Hashable, assert_ok, assert_noop, assert_err, parameter_types, decl_storage, decl_module};
use sp_core::H256;
use sp_runtime::{
	AccountId32,
	traits::{BlakeTwo256, IdentityLookup}, testing::Header,
	BuildStorage,
};
use crate as collective;

type AccountId = AccountId32;

parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MotionDuration: u64 = 3;
	pub const MaxProposals: u32 = 100;
	pub const MaxMembers: u32 = 100;
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(1024);
}
impl frame_system::Config for Test {
	type BaseCallFilter = ();
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = Call;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = BlockHashCount;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
}
impl Config<Instance1> for Test {
	type Origin = Origin;
	type Proposal = Call;
	type Event = Event;
	type MotionDuration = MotionDuration;
	type MaxProposals = MaxProposals;
	type MaxMembers = MaxMembers;
	type DefaultVote = PrimeDefaultVote;
	type WeightInfo = ();
}
impl Config<Instance2> for Test {
	type Origin = Origin;
	type Proposal = Call;
	type Event = Event;
	type MotionDuration = MotionDuration;
	type MaxProposals = MaxProposals;
	type MaxMembers = MaxMembers;
	type DefaultVote = MoreThanMajorityThenPrimeDefaultVote;
	type WeightInfo = ();
}
impl Config for Test {
	type Origin = Origin;
	type Proposal = Call;
	type Event = Event;
	type MotionDuration = MotionDuration;
	type MaxProposals = MaxProposals;
	type MaxMembers = MaxMembers;
	type DefaultVote = PrimeDefaultVote;
	type WeightInfo = ();
}

// example module to test behaviors.
pub mod example {
	use super::*;
	use frame_system::ensure_signed;
	pub trait Config: frame_system::Config { }

	decl_storage! {
		trait Store for Module<T: Config> as Example {
			pub WhoCalled: Vec<T::AccountId>;
		}
	}

	decl_module! {
		pub struct Module<T: Config> for enum Call where origin: <T as frame_system::Config>::Origin {
			#[weight = 0]
			fn store_me(
				origin,
			) -> DispatchResult {
				let who = ensure_signed(origin)?;
				WhoCalled::<T>::append(who);
				Ok(())
			}
		}
	}
}

impl example::Config for Test {}

pub type Block = sp_runtime::generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = sp_runtime::generic::UncheckedExtrinsic<u32, u64, Call, ()>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: frame_system::{Pallet, Call, Event<T>},
		Collective: collective::<Instance1>::{Pallet, Call, Event<T>, Origin<T>, Config<T>},
		CollectiveMajority: collective::<Instance2>::{Pallet, Call, Event<T>, Origin<T>, Config<T>},
		Example: example::{Pallet, Call},
	}
);

fn account(n: u32) -> AccountId {
	let hash = BlakeTwo256::hash(&n.encode());
	let account = AccountId::decode(&mut &hash[..]).unwrap_or_default();
	account
}

pub fn new_test_ext() -> sp_io::TestExternalities {
	let collective1 = (1..=3).map(account).collect::<Vec<_>>();
	let collective2 = (1..=6).map(account).collect::<Vec<_>>();
	let mut ext: sp_io::TestExternalities = GenesisConfig {
		collective_Instance1: collective::GenesisConfig {
			members: collective1,
			phantom: Default::default(),
		},
		collective_Instance2: collective::GenesisConfig {
			members: collective2,
			phantom: Default::default(),
		},
		collective: Default::default(),
	}.build_storage().unwrap().into();
	ext.execute_with(|| System::set_block_number(1));
	ext
}

#[test]
fn accounts_dont_match_instantiations() {
	// Basically, accounts are seeded on their Pallet Id and Pallet Index,
	// and these should be globally unique.
	assert_ne!(
		Collective::origin_to_ratio_account(RawOrigin::Members(1, 3), 1, 3),
		CollectiveMajority::origin_to_ratio_account(RawOrigin::Members(1, 3), 1, 3),
	);
}

#[test]
fn origin_to_ratio_account_works() {
	assert_ok!(Collective::origin_to_ratio_account(RawOrigin::Members(1, 3), 1, 3));
	assert_ok!(Collective::origin_to_ratio_account(RawOrigin::Members(2, 3), 1, 3));
	// Can't increase ratio
	assert_err!(
		Collective::origin_to_ratio_account(RawOrigin::Members(1, 3), 2, 3),
		Error::<Test, Instance1>::NotEnoughMembers,
	);
	// Can't increase member representation
	assert_err!(
		Collective::origin_to_ratio_account(RawOrigin::Members(1, 3), 2, 6),
		Error::<Test, Instance1>::NotEnoughMembers,
	);
	assert_eq!(
		Collective::origin_to_ratio_account(RawOrigin::Members(1, 3), 1, 3).unwrap(),
		Collective::origin_to_ratio_account(RawOrigin::Members(2, 6), 1, 3).unwrap(),
	);
	assert_ne!(
		Collective::origin_to_ratio_account(RawOrigin::Members(1, 3), 1, 3).unwrap(),
		Collective::origin_to_ratio_account(RawOrigin::Members(2, 6), 2, 6).unwrap(),
	);
}

#[test]
fn origin_to_quantity_account_works() {
	assert_ok!(Collective::origin_to_quantity_account(RawOrigin::Members(1, 3)));
	assert_ok!(Collective::origin_to_quantity_account(RawOrigin::Members(1, 6)));
	assert_ok!(Collective::origin_to_quantity_account(RawOrigin::Members(2, 3)));
	assert_eq!(
		Collective::origin_to_quantity_account(RawOrigin::Members(1, 3)).unwrap(),
		Collective::origin_to_quantity_account(RawOrigin::Members(1, 6)).unwrap(),
	);
	assert_ne!(
		Collective::origin_to_quantity_account(RawOrigin::Members(1, 3)).unwrap(),
		Collective::origin_to_quantity_account(RawOrigin::Members(2, 6)).unwrap(),
	);
}

#[test]
fn dispatch_with_ratio_account_works() {
	new_test_ext().execute_with(|| {
		let proposal = Call::CollectiveMajority(
			crate::Call::dispatch_as_ratio_account(
				Box::new(Call::Example(example::Call::store_me())),
				100,
				1,
				3,
			)
		);

		// Checks origin
		assert_noop!(Collective::dispatch_as_ratio_account(
				Origin::signed(Default::default()),
				Box::new(Call::Example(example::Call::store_me())),
				100,
				1,
				3,
		), DispatchError::BadOrigin);

		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let proposal_weight = proposal.get_dispatch_info().weight;
		let hash: H256 = proposal.blake2_256().into();

		// Create a call with 2 / 6
		assert_ok!(CollectiveMajority::propose(
			Origin::signed(account(1)),
			2,
			Box::new(proposal.clone()),
			proposal_len,
		));
		assert_ok!(CollectiveMajority::vote(Origin::signed(account(2)), hash.clone(), 0, true));
		assert_ok!(CollectiveMajority::close(
			Origin::signed(account(2)),
			hash.clone(),
			0,
			proposal_weight,
			proposal_len
		));

		// Should match 1/3
		assert_eq!(
			example::WhoCalled::<Test>::get(),
			vec![CollectiveMajority::origin_to_ratio_account(RawOrigin::Members(1, 3), 1, 3).unwrap()],
		);
	});
}

#[test]
fn dispatch_with_quantity_account_works() {
	new_test_ext().execute_with(|| {
		let proposal = Call::CollectiveMajority(
			crate::Call::dispatch_as_quantity_account(
				Box::new(Call::Example(example::Call::store_me())),
				100,
			)
		);

		// Checks origin
		assert_noop!(Collective::dispatch_as_quantity_account(
				Origin::signed(Default::default()),
				Box::new(Call::Example(example::Call::store_me())),
				100,
		), DispatchError::BadOrigin);

		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let proposal_weight = proposal.get_dispatch_info().weight;
		let hash: H256 = proposal.blake2_256().into();

		// Create a call with 2 / 6
		assert_ok!(CollectiveMajority::propose(
			Origin::signed(account(1)),
			2,
			Box::new(proposal.clone()),
			proposal_len,
		));
		assert_ok!(CollectiveMajority::vote(Origin::signed(account(2)), hash.clone(), 0, true));
		assert_ok!(CollectiveMajority::close(
			Origin::signed(account(2)),
			hash.clone(),
			0,
			proposal_weight,
			proposal_len
		));

		// Should match 1/3
		assert_eq!(
			example::WhoCalled::<Test>::get(),
			vec![CollectiveMajority::origin_to_quantity_account(RawOrigin::Members(2, 100)).unwrap()],
		);
	});
}
