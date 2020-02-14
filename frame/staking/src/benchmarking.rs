use super::*;
use sp_runtime::{BenchmarkResults, BenchmarkParameter};
use sp_runtime::traits::{Dispatchable, Convert, Benchmarking, BenchmarkingSetup};
use sp_io::hashing::blake2_256;
use frame_support::StorageValue;
use pallet_indices::address::Address;
use frame_system::RawOrigin;
use sp_phragmen::{
	ExtendedBalance, StakedAssignment, reduce, build_support_map, evaluate_support, PhragmenScore,
};

macro_rules! assert_ok {
	( $x:expr $(,)? ) => {
		assert_eq!($x, Ok(()));
	};
	( $x:expr, $y:expr $(,)? ) => {
		assert_eq!($x, Ok($y));
	}
}

const CTRL_PREFIX: u32 = 1000;
const NOMINATOR_PREFIX: u32 = 1_000_000;
const USER: u32 = 999_999_999;

static mut SEED: u64 = 999_666;

type AddressOf<T> = Address<<T as frame_system::Trait>::AccountId, u32>;

fn rr(a: u32, b: u32) -> u32 {
	use rand::Rng;
	use rand_chacha::rand_core::SeedableRng;
	// well, what do you expect? This is just benchmark code.
	unsafe {
		let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(SEED);
		SEED += 1;
		rng.gen_range(a, b)
	}
}

fn account<T: Trait>(index: u32) -> T::AccountId {
	let entropy = (b"benchmark/staking", index).using_encoded(blake2_256);
	T::AccountId::decode(&mut &entropy[..]).unwrap_or_default()
}

fn address<T: Trait>(index: u32) -> AddressOf<T> {
	pallet_indices::address::Address::Id(account::<T>(index))
}

fn signed<T: Trait>(who: T::AccountId) -> T::Origin {
	RawOrigin::Signed(who).into()
}

fn signed_account<T: Trait>(index: u32) -> T::Origin {
	signed::<T>(account::<T>(index))
}

fn bond_validator<T: Trait>(stash: T::AccountId, ctrl: u32, val: BalanceOf<T>)
	where T::Lookup: StaticLookup<Source=AddressOf<T>>
{
	let _ = T::Currency::make_free_balance_be(&stash, val);
	assert_ok!(<Module<T>>::bond(
		signed::<T>(stash),
		address::<T>(ctrl),
		val,
		RewardDestination::Controller
	));
	assert_ok!(<Module<T>>::validate(
		signed_account::<T>(ctrl),
		ValidatorPrefs::default()
	));
}

fn bond_nominator<T: Trait>(
	stash: T::AccountId,
	ctrl: u32,
	val: BalanceOf<T>,
	target: Vec<AddressOf<T>>
) where T::Lookup: StaticLookup<Source=AddressOf<T>> {

	let _ = T::Currency::make_free_balance_be(&stash, val);
	assert_ok!(<Module<T>>::bond(
		signed::<T>(stash),
		address::<T>(ctrl),
		val,
		RewardDestination::Controller
	));
	assert_ok!(<Module<T>>::nominate(signed_account::<T>(ctrl), target));
}

fn setup_chain_stakers<T: Trait>(
	num_stakers: u32,
	num_voters: u32,
	edge_per_voter: u32,
) where T::Lookup: StaticLookup<Source=AddressOf<T>> {
	(0..num_stakers).for_each(|i| {
		bond_validator::<T>(
			account::<T>(i),
			i + CTRL_PREFIX,
			<BalanceOf<T>>::from(rr(1, 1000)) * T::Currency::minimum_balance(),
		);
	});

	(0..num_voters).for_each(|i| {
		let mut targets: Vec<AddressOf<T>> = Vec::with_capacity(edge_per_voter as usize);
		let mut all_targets = (0..num_stakers).map(|t| address::<T>(t)).collect::<Vec<_>>();
		assert!(num_stakers >= edge_per_voter);
		(0..edge_per_voter).for_each(|_| {
			let target = all_targets.remove(rr(0, all_targets.len() as u32 - 1) as usize);
			targets.push(target);
		});
		bond_nominator::<T>(
			account::<T>(i + NOMINATOR_PREFIX),
			i + NOMINATOR_PREFIX + CTRL_PREFIX,
			<BalanceOf<T>>::from(rr(1, 1000)) * T::Currency::minimum_balance(),
			targets,
		);
	});

	<Module<T>>::create_stakers_snapshot();
}

fn get_weak_solution<T: Trait>(do_reduce: bool)
-> (Vec<ValidatorIndex>, CompactOf<T>, PhragmenScore) {
	use sp_std::collections::btree_map::BTreeMap;
	let mut backing_stake_of: BTreeMap<T::AccountId, BalanceOf<T>> = BTreeMap::new();

	// self stake
	<Validators<T>>::enumerate().for_each(|(who, _p)| {
		*backing_stake_of.entry(who.clone()).or_insert(Zero::zero()) +=
			<Module<T>>::slashable_balance_of(&who)
	});

	// add nominator stuff
	<Nominators<T>>::enumerate().for_each(|(who, nomination)| {
		nomination.targets.into_iter().for_each(|v| {
			*backing_stake_of.entry(v).or_insert(Zero::zero()) +=
				<Module<T>>::slashable_balance_of(&who)
		})
	});


	// elect winners
	let mut sorted: Vec<T::AccountId> = backing_stake_of.keys().cloned().collect();
	sorted.sort_by_key(|x| backing_stake_of.get(x).unwrap());
	let winners: Vec<T::AccountId> = sorted
		.iter()
		.cloned()
		.take(<Module<T>>::validator_count() as usize)
		.collect();

	let mut assignments: Vec<StakedAssignment<T::AccountId>> = Vec::new();
	<Nominators<T>>::enumerate().for_each(|(who, nomination)| {
		let mut dist: Vec<(T::AccountId, ExtendedBalance)> = Vec::new();
		nomination.targets.into_iter().for_each(|v| {
			if winners.iter().find(|&w| *w == v).is_some() {
				dist.push((v, ExtendedBalance::zero()));
			}
		});

		if dist.len() == 0 {
			return;
		}

		// assign real stakes. just split the stake.
		let stake = <T::CurrencyToVote as Convert<BalanceOf<T>, u64>>::convert(
			<Module<T>>::slashable_balance_of(&who),
		) as ExtendedBalance;

		let mut sum: ExtendedBalance = Zero::zero();
		let dist_len = dist.len() as ExtendedBalance;

		// assign main portion
		// only take the first half into account. This should highly imbalance stuff, which is good.
		dist
			.iter_mut()
			.take( if dist_len > 1 { (dist_len as usize) / 2 } else { 1 } )
			.for_each(|(_, w)|
		{
			let partial = stake / dist_len;
			*w = partial;
			sum += partial;
		});

		// assign the leftover to last.
		let leftover = stake - sum;
		let last = dist.last_mut().unwrap();
		last.1 += leftover;

		assignments.push(StakedAssignment {
			who,
			distribution: dist,
		});
	});

	// add self support to winners.
	winners.iter().for_each(|w| assignments.push(StakedAssignment {
		who: w.clone(),
		distribution: vec![(
			w.clone(),
			<T::CurrencyToVote as Convert<BalanceOf<T>, u64>>::convert(
				<Module<T>>::slashable_balance_of(&w)
			) as ExtendedBalance,
		)]
	}));

	let support = build_support_map::<T::AccountId>(&winners, &assignments).0;
	let score = evaluate_support(&support);

	if do_reduce {
		reduce(&mut assignments);
	}

	// helpers for building the compact
	let snapshot_validators = <Module<T>>::snapshot_validators().unwrap();
	let snapshot_nominators = <Module<T>>::snapshot_nominators().unwrap();

	let nominator_index = |a: &T::AccountId| -> Option<NominatorIndex> {
		snapshot_nominators.iter().position(|x| x == a).and_then(|i|
			<usize as TryInto<NominatorIndex>>::try_into(i).ok()
		)
	};
	let validator_index = |a: &T::AccountId| -> Option<ValidatorIndex> {
		snapshot_validators.iter().position(|x| x == a).and_then(|i|
			<usize as TryInto<ValidatorIndex>>::try_into(i).ok()
		)
	};

	// convert back to ratio assignment. This takes less space.
	let low_accuracy_assignment: Vec<Assignment<T::AccountId, OffchainAccuracy>> = assignments
		.into_iter()
		.map(|sa| sa.into_assignment(true))
		.collect();


	// compact encode the assignment.
	let compact = <CompactOf<T>>::from_assignment(
		low_accuracy_assignment,
		nominator_index,
		validator_index,
	).unwrap();

	// winners to index.
	let winners = winners.into_iter().map(|w|
		snapshot_validators.iter().position(|v| *v == w).unwrap().try_into().unwrap()
	).collect::<Vec<ValidatorIndex>>();

	(winners, compact, score)
}

fn get_seq_phragmen_solution<T: Trait>(do_reduce: bool)
-> (Vec<ValidatorIndex>, CompactOf<T>, PhragmenScore) {
	let sp_phragmen::PhragmenResult {
		winners,
		assignments,
	} = <Module<T>>::do_phragmen::<Percent>().unwrap();

	let snapshot_validators = <Module<T>>::snapshot_validators().unwrap();
	let snapshot_nominators = <Module<T>>::snapshot_nominators().unwrap();

	offchain_election::prepare_submission::<T>(
		snapshot_nominators,
		snapshot_validators,
		assignments,
		winners,
		do_reduce,
	)
}

#[cfg(test)]
fn clean<T: Trait>() {
	use frame_support::StoragePrefixedMap;

	<Validators<T>>::enumerate().for_each(|(k, _)| <Validators<T>>::remove(k));
	<Nominators<T>>::enumerate().for_each(|(k, _)| <Nominators<T>>::remove(k));
	<Stakers<T>>::remove_all();
	<Ledger<T>>::remove_all();
	<Bonded<T>>::remove_all();
	<QueuedElected<T>>::kill();
	QueuedScore::kill();
}

#[repr(u32)]
#[allow(dead_code)]
#[derive(Debug)]
pub enum BenchmarkingMode {
	/// Initial submission. This will be rather cheap
	InitialSubmission,
	/// A better submission that will replace the previous ones. This is the most expensive.
	StrongerSubmission,
	/// A weak submission that will be rejected. This will be rather cheap.
	WeakerSubmission,
}

/// Benchmark `set` extrinsic.
struct SubmitElectionSolution;
impl<T: Trait> BenchmarkingSetup<T, Call<T>, RawOrigin<T::AccountId>> for SubmitElectionSolution
	where T::Lookup: StaticLookup<Source=AddressOf<T>>
{
	fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)> {
		vec![
			// number of nominators
			(BenchmarkParameter::N, 100, 20_000),
			// number of validator candidates
			(BenchmarkParameter::V, 100, 2_000),
			// num to elect
			(BenchmarkParameter::E, 100, 1000),
			// edge per vote
			(BenchmarkParameter::Z, 2, 16),
		]
	}

	fn instance(&self, components: &[(BenchmarkParameter, u32)])
		-> Result<(Call<T>, RawOrigin<T::AccountId>), &'static str>
	{
		let num_validators = components.iter().find(|&c| c.0 == BenchmarkParameter::V).unwrap().1;
		let num_nominators = components.iter().find(|&c| c.0 == BenchmarkParameter::N).unwrap().1;
		let edge_per_voter = components.iter().find(|&c| c.0 == BenchmarkParameter::Z).unwrap().1;
		let mode: BenchmarkingMode = BenchmarkingMode::WeakerSubmission;
		let do_reduce: bool = true;
		let to_elect: u32 = components.iter().find(|&c| c.0 == BenchmarkParameter::E).unwrap().1;

		sp_std::if_std! {
			println!("++ instance with params {} / {} / {} / {:?} / {}",
				num_nominators,
				num_validators,
				edge_per_voter,
				mode,
				to_elect,
			);
		}

		if num_validators < to_elect {
			return Err("invalid setup. too few candidates");
		}

		// setup
		ValidatorCount::put(to_elect);
		MinimumValidatorCount::put(to_elect/2);
		<EraElectionStatus<T>>::put(ElectionStatus::Open(T::BlockNumber::from(1u32)));

		// stake and nominate everyone
		setup_chain_stakers::<T>(num_validators, num_nominators, edge_per_voter);

		// call data
		let (winners, compact, score) = match mode {
			BenchmarkingMode::InitialSubmission => {
				/* No need to setup anything */
				get_seq_phragmen_solution::<T>(do_reduce)
			},
			BenchmarkingMode::StrongerSubmission => {
				let (winners, compact, score) = get_weak_solution::<T>(do_reduce);
				assert_ok!(
					<Module<T>>::submit_election_solution(
						signed_account::<T>(USER),
						winners,
						compact,
						score,
					)
				);
				get_seq_phragmen_solution::<T>(do_reduce)
			},
			BenchmarkingMode::WeakerSubmission => {
				let (winners, compact, score) = get_seq_phragmen_solution::<T>(do_reduce);
				assert_ok!(
					<Module<T>>::submit_election_solution(
						signed_account::<T>(USER),
						winners,
						compact,
						score,
					)
				);
				get_weak_solution::<T>(do_reduce)
			}
		};

		// must have chosen correct number of winners.
		assert_eq!(winners.len() as u32, <Module<T>>::validator_count());

		let call = crate::Call::<T>::submit_election_solution(
			winners,
			compact,
			score,
		);

		Ok((call, RawOrigin::Signed(account::<T>(USER))))
	}
}

impl<T: Trait> Benchmarking<BenchmarkResults> for Module<T> where T::Lookup: StaticLookup<Source=AddressOf<T>> {
	fn run_benchmark(extrinsic: Vec<u8>, steps: u32, repeat: u32) -> Result<Vec<BenchmarkResults>, &'static str> {
		// warm up. why not.
		#[cfg(not(test))]
		{
			sp_io::benchmarking::commit_db();
			sp_io::benchmarking::wipe_db();
		}

		// select
		let selected_benchmark = match extrinsic.as_slice() {
			b"submit_election_solution" => SubmitElectionSolution,
			_ => return Err("Could not find extrinsic."),
		};

		// get components and params
		let components = <
			SubmitElectionSolution
			as
			BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>
		>::components(&selected_benchmark);
		let mode = BenchmarkingMode::WeakerSubmission;

		let mut results: Vec<BenchmarkResults> = Vec::new();
		for (name, low, high) in components.iter() {
			// Create up to `STEPS` steps for that component between high and low.
			let step_size = ((high - low) / steps).max(1);
			let num_of_steps = (high - low) / step_size;

			for s in 0..num_of_steps {
				// final component value.
				let component_value = low + step_size * s;

				// Select the mid value for all the other components.
				let c: Vec<(BenchmarkParameter, u32)> = components.iter()
					.map(|(n, l, h)|
						(*n, if n == name { component_value } else { (h - l) / 2 + l })
					).collect();

				for _ in 0..repeat {
					if let Ok((call, caller)) = <SubmitElectionSolution as BenchmarkingSetup<
						T,
						Call<T>,
						RawOrigin<T::AccountId>,
					>>::instance(&selected_benchmark, &c) {
						#[cfg(not(test))]
						sp_io::benchmarking::commit_db();

						let start = sp_io::benchmarking::current_time();

						match mode {
							BenchmarkingMode::WeakerSubmission => {
								// todo check the correct error is coming.
								let _ = call.dispatch(caller.into()).unwrap_err();
							},
							_ => call.dispatch(caller.into())?,
						};
						let finish = sp_io::benchmarking::current_time();

						let elapsed = finish - start;
						results.push((c.clone(), elapsed));

						#[cfg(not(test))]
						sp_io::benchmarking::wipe_db();
					} else {
						results.push((c.clone(), 0));
					}

				}
			}
		}

		Ok(results)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_runtime::traits::Benchmarking;
	use sp_runtime::BenchmarkResults;
	use frame_support::{impl_outer_origin, impl_outer_dispatch, parameter_types};

	type AccountId = u64;
	type AccountIndex = u32;
	type BlockNumber = u64;
	type Balance = u64;

	type System = frame_system::Module<Test>;
	type Balances = pallet_balances::Module<Test>;
	type Staking = crate::Module<Test>;
	type Indices = pallet_indices::Module<Test>;

	impl_outer_origin! {
		pub enum Origin for Test  where system = frame_system {}
	}

	impl_outer_dispatch! {
		pub enum Call for Test where origin: Origin {
			staking::Staking,
		}
	}

	#[derive(Clone, Eq, PartialEq, Debug)]
	pub struct Test;

	impl frame_system::Trait for Test {
		type Origin = Origin;
		type Index = AccountIndex;
		type BlockNumber = BlockNumber;
		type Call = Call;
		type Hash = sp_core::H256;
		type Hashing = ::sp_runtime::traits::BlakeTwo256;
		type AccountId = AccountId;
		type Lookup = Indices;
		type Header = sp_runtime::testing::Header;
		type Event = ();
		type BlockHashCount = ();
		type MaximumBlockWeight = ();
		type AvailableBlockRatio = ();
		type MaximumBlockLength = ();
		type Version = ();
		type ModuleToIndex = ();
		type AccountData = pallet_balances::AccountData<u64>;
		type OnNewAccount = ();
		type OnReapAccount = (Balances, Staking);
	}
	parameter_types! {
		pub const ExistentialDeposit: Balance = 0;
	}
	impl pallet_balances::Trait for Test {
		type Balance = Balance;
		type Event = ();
		type DustRemoval = ();
		type ExistentialDeposit = ExistentialDeposit;
		type AccountStore = System;
	}
	impl pallet_indices::Trait for Test {
		type AccountIndex = AccountIndex;
		type Event = ();
		type Currency = Balances;
		type Deposit = ();
	}
	parameter_types! {
		pub const MinimumPeriod: u64 = 5;
	}
	impl pallet_timestamp::Trait for Test {
		type Moment = u64;
		type OnTimestampSet = ();
		type MinimumPeriod = MinimumPeriod;
	}
	impl pallet_session::historical::Trait for Test {
		type FullIdentification = crate::Exposure<AccountId, Balance>;
		type FullIdentificationOf = crate::ExposureOf<Test>;
	}

	sp_runtime::impl_opaque_keys! {
		pub struct SessionKeys {
			pub foo: sp_runtime::testing::UintAuthorityId,
		}
	}

	pub struct TestSessionHandler;
	impl pallet_session::SessionHandler<AccountId> for TestSessionHandler {
		// EVEN if no tests break, I must have broken something here... TODO
		const KEY_TYPE_IDS: &'static [sp_runtime::KeyTypeId] = &[];

		fn on_genesis_session<Ks: sp_runtime::traits::OpaqueKeys>(_validators: &[(AccountId, Ks)]) {}

		fn on_new_session<Ks: sp_runtime::traits::OpaqueKeys>(
			_: bool,
			_: &[(AccountId, Ks)],
			_: &[(AccountId, Ks)],
		) {}

		fn on_disabled(_: usize) {}
	}

	impl pallet_session::Trait for Test {
		type SessionManager = pallet_session::historical::NoteHistoricalRoot<Test, Staking>;
		type Keys = SessionKeys;
		type ShouldEndSession = pallet_session::PeriodicSessions<(), ()>;
		type SessionHandler = TestSessionHandler;
		type Event = ();
		type ValidatorId = AccountId;
		type ValidatorIdOf = crate::StashOf<Test>;
		type DisabledValidatorsThreshold = ();
	}
	pallet_staking_reward_curve::build! {
		const I_NPOS: sp_runtime::curve::PiecewiseLinear<'static> = curve!(
			min_inflation: 0_025_000,
			max_inflation: 0_100_000,
			ideal_stake: 0_500_000,
			falloff: 0_050_000,
			max_piece_count: 40,
			test_precision: 0_005_000,
		);
	}
	parameter_types! {
		pub const RewardCurve: &'static sp_runtime::curve::PiecewiseLinear<'static> = &I_NPOS;
	}

	pub type Extrinsic = sp_runtime::testing::TestXt<Call, ()>;
	type SubmitTransaction = frame_system::offchain::TransactionSubmitter<
		sp_runtime::testing::UintAuthorityId,
		Test,
		Extrinsic,
	>;

	impl crate::Trait for Test {
		type Currency = Balances;
		type Time = pallet_timestamp::Module<Self>;
		type CurrencyToVote = mock::CurrencyToVoteHandler;
		type RewardRemainder = ();
		type Event = ();
		type Slash = ();
		type Reward = ();
		type SessionsPerEra = ();
		type SlashDeferDuration = ();
		type SlashCancelOrigin = frame_system::EnsureRoot<Self::AccountId>;
		type BondingDuration = ();
		type SessionInterface = Self;
		type RewardCurve = RewardCurve;
		type NextSessionChange = mock::PeriodicSessionChange<()>;
		type ElectionLookahead = ();
		type Call = Call;
		type SubmitTransaction = SubmitTransaction;
		type KeyType = mock::dummy_sr25519::AuthorityId;
	}


	fn new_test_ext() -> sp_io::TestExternalities {
		frame_system::GenesisConfig::default().build_storage::<Test>().unwrap().into()
	}

	#[test]
	fn benchmarking_setup_should_work() {
		new_test_ext().execute_with(|| {
			let _ = <Staking as Benchmarking<BenchmarkResults>>::run_benchmark(
				Default::default(),
				Default::default(),
				1,
			);
		})
	}
}
