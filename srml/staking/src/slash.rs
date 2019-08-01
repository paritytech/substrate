// Copyright 2017-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Slashing mod
//!
//! This is currently located in `Staking` because it has dependency to `Exposure`

use crate::Exposure;
use srml_support::{
	StorageMap, decl_module, decl_storage,
	traits::{Currency, WindowLength, DoSlash, DoReward}
};
use parity_codec::{HasCompact, Codec, Decode, Encode};
use rstd::{vec::Vec, collections::{btree_map::BTreeMap, btree_set::BTreeSet}};
use sr_primitives::{Perbill, traits::{MaybeSerializeDebug, Zero}};

type BalanceOf<T> =
	<<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;

/// Slashing trait
pub trait Trait: system::Trait {
	/// Slashing kind
	type SlashKind: Copy + Clone + Codec + MaybeSerializeDebug + WindowLength<u32>;
	/// Currency
	type Currency: Currency<Self::AccountId>;
}

/// State of a slashed entity
#[derive(Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct SlashState<AccountId, Balance: HasCompact> {
	exposure: Exposure<AccountId, Balance>,
	slashed_amount: SlashAmount<AccountId, Balance>,
}

/// Slashed amount for a entity including its nominators
#[derive(Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct SlashAmount<AccountId, Balance> {
	own: Balance,
	others: BTreeMap<AccountId, Balance>,
}

decl_storage! {
	trait Store for Module<T: Trait> as RollingWindow {
		/// Slashing history
		SlashHistory get(misbehavior_reports): linked_map T::SlashKind =>
			BTreeMap<T::AccountId, SlashState<T::AccountId, BalanceOf<T>>>;
	}
}

decl_module! {
	/// Slashing module
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
}

impl<T: Trait> Module<T> {

	/// Tries to adjust the `slash` based on `new_slash` and `prev_slash`
	///
	/// Returns the total slashed amount
	fn adjust_slash(
		who: &T::AccountId,
		new_slash: BalanceOf<T>,
		prev_slash: BalanceOf<T>,
		slashed_amount: &mut BalanceOf<T>,
	) -> BalanceOf<T> {
		if new_slash > prev_slash {
			let amount = new_slash - prev_slash;
			T::Currency::slash(who, amount);
			*slashed_amount = *slashed_amount + amount;
			new_slash
		} else {
			prev_slash
		}
	}

	fn update_exposure_for_known(
		who: &T::AccountId,
		prev_state: &mut SlashState<T::AccountId, BalanceOf<T>>,
		exposure: &Exposure<T::AccountId, BalanceOf<T>>,
		severity: Perbill,
		slashed_amount: &mut BalanceOf<T>,
	) {
		let new_slash = severity * exposure.own;

		Self::adjust_slash(&who, new_slash, prev_state.slashed_amount.own, slashed_amount);

		let intersection: BTreeSet<T::AccountId> = exposure.others
			.iter()
			.filter_map(|e1| prev_state.exposure.others.iter().find(|e2| e1.who == e2.who))
			.map(|e| e.who.clone())
			.collect();

		let previous_slash = rstd::mem::replace(&mut prev_state.slashed_amount.others, BTreeMap::new());

		for nominator in &exposure.others {
			let new_slash = severity * nominator.value;

			// make sure that we are not double slashing
			let prev = if intersection.contains(&nominator.who) {
				previous_slash.get(&nominator.who).cloned().unwrap_or_else(|| Zero::zero())
			} else {
				Zero::zero()
			};

			Self::adjust_slash(&nominator.who, new_slash, prev, slashed_amount);
			prev_state.slashed_amount.others.insert(nominator.who.clone(), new_slash);
		}

		prev_state.exposure = exposure.clone();
		prev_state.slashed_amount.own = new_slash;
	}

	/// Updates the history of slashes based on the new severity and only apply new slash
	/// if the estimated `slash_amount` exceeds the `previous slash_amount`
	///
	/// Returns the `true` if `who` was already in the history otherwise `false`
	fn mutate_slash_history(
		who: &T::AccountId,
		exposure: &Exposure<T::AccountId, BalanceOf<T>>,
		severity: Perbill,
		kind: T::SlashKind,
		total_slash: &mut BalanceOf<T>,
	) -> bool {
		<SlashHistory<T>>::mutate(kind, |state| {

			let mut in_history = false;

			for (stash, s) in state.iter_mut() {
				if stash == who {
					Self::update_exposure_for_known(stash, s, exposure, severity, total_slash);
					in_history = true;
				} else {
					s.slashed_amount.own = Self::adjust_slash(
						stash,
						severity * s.exposure.own,
						s.slashed_amount.own,
						total_slash
					);

					for nominator in &s.exposure.others {
						let new_slash = severity * nominator.value;
						if let Some(prev) = s.slashed_amount.others.get_mut(&nominator.who) {
							*prev = Self::adjust_slash(&nominator.who, new_slash, *prev, total_slash);
						} else {
							Self::adjust_slash(&nominator.who, new_slash, Zero::zero(), total_slash);
							s.slashed_amount.others.insert(nominator.who.clone(), new_slash);
						}
					}
				}
			}

			in_history
		})
	}
}

impl<T: Trait> DoSlash<(T::AccountId, Exposure<T::AccountId, BalanceOf<T>>), Perbill, T::SlashKind> for Module<T>
{
	type SlashedEntries = Vec<(T::AccountId, Exposure<T::AccountId, BalanceOf<T>>)>;
	type SlashedAmount = BalanceOf<T>;

	fn do_slash(
		(who, exposure): (T::AccountId, Exposure<T::AccountId, BalanceOf<T>>),
		severity: Perbill,
		kind: T::SlashKind,
	) -> Result<(Self::SlashedEntries, Self::SlashedAmount), ()> {

		let mut total_slash = Zero::zero();
		let who_exist = <Module<T>>::mutate_slash_history(&who, &exposure, severity, kind, &mut total_slash);

		if !who_exist {
			let amount = severity * exposure.own;
			Self::adjust_slash(&who, amount, Zero::zero(), &mut total_slash);
			let mut slashed_amount = SlashAmount { own: amount, others: BTreeMap::new() };

			for nominator in &exposure.others {
				let amount = severity * nominator.value;
				Self::adjust_slash(&nominator.who, amount, Zero::zero(), &mut total_slash);
				slashed_amount.others.insert(nominator.who.clone(), amount);
			}

			<SlashHistory<T>>::mutate(kind, |state| {
				state.insert(who, SlashState { exposure, slashed_amount });
			});
		}

		let slashed_entities = <SlashHistory<T>>::get(kind)
			.iter()
			.map(|(who, state)| (who.clone(), state.exposure.clone()))
			.collect();

		Ok((slashed_entities, total_slash))
	}
}

impl<T: Trait, Reporters> DoReward<Reporters, BalanceOf<T>> for Module<T>
where
	Reporters: IntoIterator<Item = (T::AccountId, Perbill)>,
{
	fn do_reward(reporters: Reporters, reward: BalanceOf<T>) -> Result<(), ()> {
		let mut reward_pot = reward;

		for (reporter, fraction) in reporters {
			let amount = rstd::cmp::min(fraction * reward, reward_pot);
			reward_pot -= amount;
			// This will fail in the account is not existing ignore it for now
			let _ = T::Currency::deposit_into_existing(&reporter, amount);
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		Exposure, IndividualExposure, Validators,
		slash::{Trait, Module as SlashingModule},
		mock::*
	};
	use rstd::cell::RefCell;
	use runtime_io::with_externalities;
	use sr_primitives::{Perbill, traits::Hash};
	use srml_rolling_window::{
		Module as RollingWindow, MisbehaviorReporter, GetMisbehaviors, impl_base_severity, impl_kind
	};
	use srml_support::{assert_ok, traits::{ReportSlash, DoSlash, AfterSlash, KeyOwnerProofSystem}};
	use std::collections::HashMap;
	use std::marker::PhantomData;
	use primitives::H256;

	type Balances = balances::Module<Test>;

	thread_local! {
		static EXPOSURES: RefCell<HashMap<AccountId, Exposure<AccountId, Balance>>> =
			RefCell::new(Default::default());
	}

	/// Trait for reporting slashes
	pub trait ReporterTrait: srml_rolling_window::Trait<MisbehaviorKind = Kind> + Trait {
		/// Key that identifies the owner
		type KeyOwner: KeyOwnerProofSystem<Self::AccountId>;

		type Reporter;

		type BabeEquivocation: ReportSlash<
			Self::Hash,
			Self::Reporter,
			<<Self as ReporterTrait>::KeyOwner as KeyOwnerProofSystem<Self::AccountId>>::FullIdentification
		>;
	}

	impl Trait for Test {
		type SlashKind = Kind;
		type Currency = Balances;
	}

	impl ReporterTrait for Test {
		type KeyOwner = FakeProver<Test>;
		type BabeEquivocation = BabeEquivocation<
			Self, SlashingModule<Test>, SlashingModule<Test>, crate::AfterSlashing<Test>
		>;
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

	impl<T> KeyOwnerProofSystem<u64> for FakeProver<T> {
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

	/// This should be something similar to `decl_module!` macro
	pub struct BabeEquivocation<T, DS, DR, AS>(PhantomData<(T, DS, DR, AS)>);

	impl_base_severity!(BabeEquivocation<T, DS, DR, AS>, Perbill: Perbill::zero());
	impl_kind!(BabeEquivocation<T, DS, DR, AS>, Kind: Kind::One);

	impl<T, DS, DR, AS> BabeEquivocation<T, DS, DR, AS> {
		pub fn as_misconduct_level(severity: Perbill) -> u8 {
			if severity > Perbill::from_percent(10) {
				4
			} else if severity > Perbill::from_percent(1) {
				3
			} else if severity > Perbill::from_rational_approximation(1_u32, 1000_u32) {
				2
			} else {
				1
			}
		}
	}

	impl<T, Reporters, Who, DS, DR, AS> ReportSlash<T::Hash, Reporters, Who> for BabeEquivocation<T, DS, DR, AS>
	where
		T: ReporterTrait,
		DS: DoSlash<Who, Perbill, Kind>,
		DR: DoReward<Reporters, DS::SlashedAmount>,
		AS: AfterSlash<DS::SlashedEntries, u8>,
		DS::SlashedAmount: rstd::fmt::Debug,
	{
		fn slash(footprint: T::Hash, reporters: Reporters, who: Who) -> Result<(), ()> {
			let kind = Self::kind();
			let _base_seve = Self::base_severity();

			RollingWindow::<T>::report_misbehavior(kind, footprint, 0)?;
			let num_violations = RollingWindow::<T>::get_misbehaviors(kind);

			// number of validators
			let n = 50;

			// example how to estimate severity
			// 3k / n^2
			let severity = Perbill::from_rational_approximation(3 * num_violations, n * n);

			let misconduct_level = Self::as_misconduct_level(severity);
			let (slashed, total_slash) = DS::do_slash(who, severity, kind)?;

			// hard code reward to 10% of the total amount
			let reward_amount = Perbill::from_percent(10) * total_slash;

			// the remaining 90% should go somewhere else, perhaps the `treasory module`?!

			// ignore if rewarding failed, because we need still to update the state of the validators
			let _ = DR::do_reward(reporters, reward_amount);
			AS::after_slash(slashed, misconduct_level);

			Ok(())
		}
	}

	#[test]
	fn slash_should_keep_state_and_increase_slash_for_history_without_nominators() {
		let misbehaved: Vec<u64> = (0..10).collect();
		let reporter = (99_u64, Perbill::one());

		with_externalities(&mut ExtBuilder::default()
			.build(),
		|| {
			let _ = Balances::make_free_balance_be(&reporter.0, 50);
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


			let mut last_slash = 0;
			let mut last_balance = 50;

			// after every slash, the slash history and slash that occurred should be included in the reward
			for (i, who) in misbehaved.iter().enumerate() {
				let i = i as u64;
				assert_ok!(BabeEquivocationReporter::<Test>::report_equivocation(FakeProof::new(*who), vec![reporter]));
				let slash = Perbill::from_rational_approximation(3 * (i + 1), 2500_u64) * 1000;
				let total_slash = slash + (slash - last_slash) * i;
				let reward = Perbill::from_percent(10) * total_slash;
				assert_eq!(Balances::free_balance(&reporter.0), last_balance + reward);
				last_balance = Balances::free_balance(&reporter.0);
				last_slash = slash;
			}

			for who in &misbehaved {
				assert_eq!(Balances::free_balance(who), 988, "should slash 1.2%");
			}

		});
	}

	#[test]
	fn slash_with_nominators_simple() {
		let misbehaved = 1;

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
						IndividualExposure { who: nom_1, value: 1500 },
						IndividualExposure { who: nom_2, value: 700 },
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

			for who in &misbehaved {
				assert_eq!(Balances::free_balance(who), 997, "should slash 0.36%");
			}
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

	// note, this test hooks in the `staking` and uses its `AfterSlash` implementation
	#[test]
	fn simple_with_after_slash() {
		with_externalities(&mut ExtBuilder::default()
			.build(),
		|| {
			let m1 = 11;
			let c1 = 10;
			let m2 = 21;
			let c2 = 20;
			let nom = 101;
			let exp1 = Staking::stakers(m1);
			let exp2 = Staking::stakers(m2);
			let initial_balance_m1 = Balances::free_balance(&m1);
			let initial_balance_m2 = Balances::free_balance(&m2);
			let initial_balance_nom = Balances::free_balance(&nom);

			// m1 (stash) -> c1 (controller)
			// m2 (stash) -> c2 (controller)
			assert_eq!(Staking::bonded(&m1), Some(c1));
			assert_eq!(Staking::bonded(&m2), Some(c2));
			assert!(<Validators<Test>>::exists(&m1));
			assert!(<Validators<Test>>::exists(&m2));

			assert_eq!(
				exp1,
				Exposure { total: 1250, own: 1000, others: vec![ IndividualExposure { who: nom, value: 250 }] }
			);
			assert_eq!(
				exp2,
				Exposure { total: 1250, own: 1000, others: vec![ IndividualExposure { who: nom, value: 250 }] }
			);

			EXPOSURES.with(|x| {
				x.borrow_mut().insert(m1, exp1);
				x.borrow_mut().insert(m2, exp2)
			});

			assert_ok!(BabeEquivocationReporter::<Test>::report_equivocation(FakeProof::new(m1), vec![]));
			assert_eq!(Balances::free_balance(&m1), initial_balance_m1 - 1, "should slash 0.12% of 1000");
			assert_eq!(Balances::free_balance(&m2), initial_balance_m2, "no misconducts yet; no slash");
			assert_eq!(Balances::free_balance(&nom), initial_balance_nom, "0.12% of 250 is zero, don't slash anything");

			assert!(is_disabled(c1), "m1 has misconduct level 2 should be disabled by now");
			assert!(!<Validators<Test>>::exists(&m1), "m1 is misconducter shall be disregard from next election");
			assert!(!is_disabled(c2), "m2 is not a misconducter; still available");
			assert!(<Validators<Test>>::exists(&m2), "no misconducts yet; still a candidate");

			assert_ok!(BabeEquivocationReporter::<Test>::report_equivocation(FakeProof::new(m2), vec![]));

			assert_eq!(Balances::free_balance(&m1), initial_balance_m1 - 2, "should slash 0.24% of 1000");
			assert_eq!(Balances::free_balance(&m2), initial_balance_m2 - 2, "should slash 0.24% of 1000");
			assert_eq!(Balances::free_balance(&nom), initial_balance_nom, "0.12% of 250 is zero, don't slash anything");

			assert!(is_disabled(c1), "m1 has misconduct level 2 should be disabled by now");
			assert!(!<Validators<Test>>::exists(&m1), "m1 is misconducter shall be disregard from next election");
			assert!(is_disabled(c2), "m2 has misconduct level 2 should be disabled by now");
			assert!(!<Validators<Test>>::exists(&m2), "m2 has misconduct level 2 should be disabled by now");

			// ensure m1 and m2 are still trusted by its nominator
			assert_eq!(Staking::nominators(nom).contains(&m1), true);
			assert_eq!(Staking::nominators(nom).contains(&m2), true);

			// increase severity to level 3
			// note, this only reports misconducts from `m2` but `m1` should be updated as well.
			for _ in 0..10 {
				assert_ok!(BabeEquivocationReporter::<Test>::report_equivocation(FakeProof::new(m2), vec![]));
			}

			// ensure m1 and m2 are not trusted by its nominator anymore
			assert_eq!(Staking::nominators(nom).contains(&m1), false);
			assert_eq!(Staking::nominators(nom).contains(&m2), false);

			assert_eq!(Staking::stakers(m1).total, 0);
			assert_eq!(Staking::stakers(m2).total, 0);
		});
	}

	#[test]
	fn rewarding() {
		with_externalities(&mut ExtBuilder::default()
			.build(),
		|| {

			let m = 0;
			let balance = u32::max_value() as u64;
			let _ = Balances::make_free_balance_be(&m, balance);

			EXPOSURES.with(|x| x.borrow_mut().insert(m, Exposure {
				own: balance,
				total: balance,
				others: vec![],
			}));

			let reporters = vec![
				(1, Perbill::from_percent(50)),
				(2, Perbill::from_percent(20)),
				(3, Perbill::from_percent(15)),
				(4, Perbill::from_percent(10)),
				(5, Perbill::from_percent(50)),
			];

			// reset balance to 1 for the reporter
			for who in 1..=5 {
				let _ = Balances::make_free_balance_be(&who, 1);
			}

			// slashed amount: 5153960 (0,0132 * 4294967295) will be slashed
			// 515396 (0.1 * 5153961) will be shared among the reporters
			assert_ok!(BabeEquivocationReporter::<Test>::report_equivocation(FakeProof::new(m), reporters));

			assert_eq!(Balances::free_balance(&1), 257698 + 1);
			assert_eq!(Balances::free_balance(&2), 103079 + 1);
			assert_eq!(Balances::free_balance(&3), 77309 + 1);
			assert_eq!(Balances::free_balance(&4), 51539 + 1);
			assert_eq!(Balances::free_balance(&5), 25771 + 1, "should only get what's left in the pot; 5% not 50%");
		});
	}
}
