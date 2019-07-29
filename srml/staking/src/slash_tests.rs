#![cfg(test)]

use crate::*;
use std::marker::PhantomData;
use srml_support::{assert_ok, traits::{ReportSlash, DoSlash, AfterSlash, KeyOwnerProofSystem}};
use crate::mock::*;
use runtime_io::with_externalities;
use srml_rolling_window::{Module as RollingWindow, MisbehaviorReporter, GetMisbehaviors,
	impl_base_severity, impl_kind};
use substrate_primitives::H256;
use primitives::traits::Hash;
use std::collections::HashMap;
use rstd::cell::RefCell;

type Balances = balances::Module<Test>;

thread_local! {
	static EXPOSURES: RefCell<HashMap<AccountId, Exposure<AccountId, Balance>>> =
		RefCell::new(Default::default());
}

/// Trait for reporting slashes
pub trait ReporterTrait: srml_rolling_window::Trait<MisbehaviorKind = Kind> {
	/// Key that identifies the owner
	type KeyOwner: KeyOwnerProofSystem<Self::AccountId>;

	type Reporter;

	/// Type of slashing
	///
	/// FullId - is the full identification of the entity to slash
	/// which may be (AccountId, Exposure)
	type BabeEquivocation: ReportSlash<
		Self::Hash,
		Self::Reporter,
		<<Self as ReporterTrait>::KeyOwner as KeyOwnerProofSystem<Self::AccountId>>::FullIdentification
	>;
}

impl ReporterTrait for Test {
	type KeyOwner = FakeProver<Test>;
	type BabeEquivocation = BabeEquivocation<Self, StakingSlasher<Test>, StakingSlasher<Test>>;
	type Reporter = Vec<(u64, Perbill)>;
}

#[derive(Debug, Clone, Encode, Decode, PartialEq)]
pub struct FakeProof<H, Proof, AccountId> {
	first_header: H,
	second_header: H,
	author: AccountId,
	membership_proof: Proof,
}

impl FakeProof<H256, Vec<u8>, AccountId> {
	fn new(author: AccountId) -> Self {
		Self {
			first_header: Default::default(),
			second_header: Default::default(),
			author,
			membership_proof: Vec::new()
		}
	}
}

pub struct FakeProver<T>(PhantomData<T>);

impl<T: ReporterTrait> KeyOwnerProofSystem<u64> for FakeProver<T> {
	type Proof = Vec<u8>;
	type FullIdentification = (u64, Exposure<u64, u64>);

	fn prove(_who: u64) -> Option<Self::Proof> {
		Some(Vec::new())
	}

	fn check_proof(who: u64, _proof: Self::Proof) -> Option<Self::FullIdentification> {
		if let Some(exp) = EXPOSURES.with(|x| x.borrow().get(&who).cloned()) {
			Some((who, exp))
		} else {
			None
		}
	}
}

pub struct BabeEquivocationReporter<T>(PhantomData<T>);

impl<T: ReporterTrait> BabeEquivocationReporter<T> {

	/// Report an equivocation
	pub fn report_equivocation(
		proof: FakeProof<
			T::Hash,
			<<T as ReporterTrait>::KeyOwner as KeyOwnerProofSystem<T::AccountId>>::Proof,
			T::AccountId
		>,
		reporters: <T as ReporterTrait>::Reporter,
	) -> Result<(), ()> {
		let identification = match T::KeyOwner::check_proof(proof.author.clone(), proof.membership_proof) {
			Some(id) => id,
			None => return Err(()),
		};

		// ignore equivocation slot for this test
		let nonce = H256::random();
		let footprint = T::Hashing::hash_of(&(0xbabe, proof.author, nonce));

		T::BabeEquivocation::slash(footprint, reporters, identification)
	}
}

pub struct BabeEquivocation<T, DS, AS>(PhantomData<(T, DS, AS)>);

impl_base_severity!(BabeEquivocation<T, DS, AS>, Perbill: Perbill::zero());
impl_kind!(BabeEquivocation<T, DS, AS>, Kind: Kind::One);

impl<T, DS, AS> BabeEquivocation<T, DS, AS> {
	pub fn as_misconduct_level(severity: Perbill) -> u8 {
		if severity >= Perbill::from_percent(1) {
			3
		} else {
			1
		}
	}
}

impl<T, Reporter, Who, DS, AS> ReportSlash<T::Hash, Reporter, Who> for BabeEquivocation<T, DS, AS>
where
	Who: Clone,
	T: ReporterTrait,
	DS: DoSlash<Who, Reporter, Perbill, Kind>,
	AS: AfterSlash<u8, Who>,
{
	fn slash(footprint: T::Hash, reporter: Reporter, who: Who) -> Result<(), ()> {
		let kind = Self::kind();
		let _base_seve = Self::base_severity();

		RollingWindow::<T>::report_misbehavior(kind, footprint, 0)?;
		let num_violations = RollingWindow::<T>::get_misbehaviors(kind);

		// number of validators
		let n = 50;

		// example how to estimate severity
		// 3k / n^2
		let severity = Perbill::from_rational_approximation(3 * num_violations, n * n);
		println!("num_violations: {:?}", num_violations);

		DS::do_slash(who.clone(), reporter, severity, kind)?;
		AS::after_slash(Self::as_misconduct_level(severity), who);

		Ok(())
	}
}

#[test]
fn it_works() {
	with_externalities(&mut ExtBuilder::default()
		.build(),
	|| {
		let who: AccountId = 0;

		EXPOSURES.with(|x| {
			let exp = Exposure {
				own: 1000,
				total: 1000,
				others: Vec::new(),
			};
			x.borrow_mut().insert(who, exp)
		});

		let _ = Balances::make_free_balance_be(&who, 1000);
		assert_eq!(Balances::free_balance(&who), 1000);

		assert_ok!(BabeEquivocationReporter::<Test>::report_equivocation(FakeProof::new(who), vec![]));
		assert_eq!(Balances::free_balance(&who), 999);
	});
}

#[test]
fn slash_should_keep_state_and_increase_slash_for_history_without_nominators() {
	let misbehaved: Vec<u64> = (0..10).collect();

	with_externalities(&mut ExtBuilder::default()
		.build(),
	|| {
		EXPOSURES.with(|x| {
			for who in &misbehaved {
				let exp = Exposure {
					own: 1000,
					total: 1000,
					others: Vec::new(),
				};
				let _ = Balances::make_free_balance_be(who, 1000);
				x.borrow_mut().insert(*who, exp);
			}
		});

		for who in &misbehaved {
			assert_ok!(BabeEquivocationReporter::<Test>::report_equivocation(FakeProof::new(*who), vec![]));
		}

		for who in &misbehaved {
			assert_eq!(Balances::free_balance(who), 988, "should slash 1.2%");
		}
	});
}

#[test]
fn slash_with_nominators_simple() {
	let misbehaved = 0;

	let nom_1 = 11;
	let nom_2 = 12;

	with_externalities(&mut ExtBuilder::default()
		.build(),
	|| {
		let _ = Balances::make_free_balance_be(&nom_1, 10_000);
		let _ = Balances::make_free_balance_be(&nom_2, 50_000);
		let _ = Balances::make_free_balance_be(&misbehaved, 9_000);
		assert_eq!(Balances::free_balance(&misbehaved), 9_000);
		assert_eq!(Balances::free_balance(&nom_1), 10_000);
		assert_eq!(Balances::free_balance(&nom_2), 50_000);

		EXPOSURES.with(|x| {
			let exp = Exposure {
				own: 9_000,
				total: 11_200,
				others: vec![
					IndividualExposure { who: 11, value: 1500 },
					IndividualExposure { who: 12, value: 700 },
				],
			};
			x.borrow_mut().insert(misbehaved, exp);
		});

		assert_ok!(BabeEquivocationReporter::<Test>::report_equivocation(FakeProof::new(misbehaved), vec![]));

		assert_eq!(Balances::free_balance(&misbehaved), 8_990, "should slash 0.12%");
		assert_eq!(Balances::free_balance(&nom_1), 9_999, "should slash 0.12% of exposure not total balance");
		assert_eq!(Balances::free_balance(&nom_2), 50_000, "should slash 0.12% of exposure not total balance");
	});
}

#[test]
fn slash_should_keep_state_and_increase_slash_for_history_with_nominators() {
	let misbehaved: Vec<u64> = (0..3).collect();

	let nom_1 = 11;
	let nom_2 = 12;

	with_externalities(&mut ExtBuilder::default()
		.build(),
	|| {
		let _ = Balances::make_free_balance_be(&nom_1, 10_000);
		let _ = Balances::make_free_balance_be(&nom_2, 50_000);

		EXPOSURES.with(|x| {
			for &who in &misbehaved {
				let exp = Exposure {
					own: 1000,
					total: 1500,
					others: vec![
						IndividualExposure { who: nom_1, value: 300 },
						IndividualExposure { who: nom_2, value: 200 },
					],
				};
				let _ = Balances::make_free_balance_be(&who, 1000);
				x.borrow_mut().insert(who, exp);
			}
		});

		for who in &misbehaved {
			assert_eq!(Balances::free_balance(who), 1000);
		}

		for who in &misbehaved {
			assert_ok!(BabeEquivocationReporter::<Test>::report_equivocation(FakeProof::new(*who), vec![]));
		}

		assert_eq!(Balances::free_balance(&0), 997, "should slash 0.36%");
		assert_eq!(Balances::free_balance(&1), 997, "should slash 0.36%");
		assert_eq!(Balances::free_balance(&2), 997, "should slash 0.36%");
		// (300 * 0.0036) * 3 = 3
		assert_eq!(Balances::free_balance(&nom_1), 9_997, "should slash 0.36%");
		// (200 * 0.0036) * 3 = 0
		assert_eq!(Balances::free_balance(&nom_2), 50_000, "should slash 0.36%");
	});
}

#[test]
fn slash_update_exposure_when_same_validator_gets_slashed_twice() {
	let misbehaved = 0;

	let nom_1 = 11;
	let nom_2 = 12;
	let nom_3 = 13;

	with_externalities(&mut ExtBuilder::default()
		.build(),
	|| {
		let _ = Balances::make_free_balance_be(&nom_1, 10_000);
		let _ = Balances::make_free_balance_be(&nom_2, 50_000);
		let _ = Balances::make_free_balance_be(&nom_3, 5_000);
		let _ = Balances::make_free_balance_be(&misbehaved, 1000);


		let exp1 = Exposure {
				own: 1_000,
				total: 31_000,
				others: vec![
					IndividualExposure { who: nom_1, value: 5_000 },
					IndividualExposure { who: nom_2, value: 25_000 },
				],
		};

		EXPOSURES.with(|x| x.borrow_mut().insert(misbehaved, exp1));

		assert_ok!(BabeEquivocationReporter::<Test>::report_equivocation(FakeProof::new(misbehaved), vec![]));

		assert_eq!(Balances::free_balance(&misbehaved), 999, "should slash 0.12%");
		assert_eq!(Balances::free_balance(&nom_1), 9_994, "should slash 0.12%");
		assert_eq!(Balances::free_balance(&nom_2), 49_970, "should slash 0.12%");
		assert_eq!(Balances::free_balance(&nom_3), 5_000, "not exposed should not be slashed");

		let exp2 = Exposure {
				own: 999,
				total: 16098,
				others: vec![
					IndividualExposure { who: nom_1, value: 10_000 },
					IndividualExposure { who: nom_2, value: 100 },
					IndividualExposure { who: nom_3, value: 4_999 },
				],
		};

		// change exposure for `misbehaved
		EXPOSURES.with(|x| x.borrow_mut().insert(misbehaved, exp2));
		assert_ok!(BabeEquivocationReporter::<Test>::report_equivocation(FakeProof::new(misbehaved), vec![]));

		// exposure is 999 so slashed based on that amount but revert previous slash
		// -> 999 * 0.0024 = 2, -> 1000 - 2 = 998
		assert_eq!(Balances::free_balance(&misbehaved), 998, "should slash 0.24%");
		assert_eq!(Balances::free_balance(&nom_1), 9_976, "should slash 0.24%");
		assert_eq!(Balances::free_balance(&nom_2), 49_970, "exposed but slash is smaller previous is still valid");
		// exposure is 4999, slash 0.0024 * 4999 -> 11
		// 5000 - 11 = 4989
		assert_eq!(Balances::free_balance(&nom_3), 4_989, "should slash 0.24%");
	});
}
