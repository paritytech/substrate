#![feature(prelude_import)]
#[prelude_import]
use std::prelude::v1::*;
#[macro_use]
extern crate std;
use sp_std::prelude::*;
pub mod onchain {
	use crate::{ElectionProvider, Error};
	use sp_arithmetic::PerThing;
	use sp_npos_elections::{
		ElectionResult, ExtendedBalance, FlatSupportMap, FlattenSupportMap, IdentifierT, VoteWeight,
	};
	use sp_std::{collections::btree_map::BTreeMap, prelude::*};
	pub struct OnChainSequentialPhragmen;
	impl<AccountId: IdentifierT> ElectionProvider<AccountId> for OnChainSequentialPhragmen {
		fn elect<P: sp_arithmetic::PerThing>(
			to_elect: usize,
			targets: Vec<AccountId>,
			voters: Vec<(AccountId, VoteWeight, Vec<AccountId>)>,
		) -> Result<FlatSupportMap<AccountId>, Error>
		where
			ExtendedBalance: From<<P as PerThing>::Inner>,
			P: sp_std::ops::Mul<ExtendedBalance, Output = ExtendedBalance>,
		{
			let mut stake_map: BTreeMap<AccountId, VoteWeight> = BTreeMap::new();
			voters.iter().for_each(|(v, s, _)| {
				stake_map.insert(v.clone(), *s);
			});
			let stake_of = Box::new(|w: &AccountId| -> VoteWeight {
				stake_map.get(w).cloned().unwrap_or_default()
			});
			sp_npos_elections::seq_phragmen::<_, P>(to_elect, targets, voters, None)
				.and_then(|e| {
					let ElectionResult {
						winners,
						assignments,
					} = e;
					let staked = sp_npos_elections::assignment_ratio_to_staked_normalized(
						assignments,
						&stake_of,
					)?;
					let winners = sp_npos_elections::to_without_backing(winners);
					sp_npos_elections::build_support_map(&winners, &staked).map(|s| s.flatten())
				})
				.map_err(From::from)
		}
		fn ongoing() -> bool {
			false
		}
	}
}
pub mod two_phase {
	use crate::{onchain::OnChainSequentialPhragmen, ElectionDataProvider, ElectionProvider};
	use codec::{Decode, Encode, HasCompact};
	use frame_support::{
		decl_error, decl_event, decl_module, decl_storage,
		dispatch::DispatchResultWithPostInfo,
		ensure,
		traits::{Currency, Get, OnUnbalanced, ReservableCurrency},
		weights::Weight,
	};
	use frame_system::{ensure_none, ensure_signed};
	use sp_npos_elections::{
		evaluate_support, generate_solution_type, Assignment, ElectionScore, ExtendedBalance,
		FlatSupportMap, FlattenSupportMap, VoteWeight,
	};
	use sp_runtime::{traits::Zero, PerThing, PerU16, Perbill, RuntimeDebug};
	use sp_std::{mem::size_of, prelude::*};
	pub mod signed {
		use crate::two_phase::*;
		use codec::Encode;
		use sp_arithmetic::traits::SaturatedConversion;
		use sp_npos_elections::is_score_better;
		impl<T: Trait> Module<T> {
			/// Start the signed phase.
			///
			/// Upon calling this, auxillary data for election is stored and signed solutions will be
			/// accepted.
			///
			/// The signed phase must always start before the unsigned phase.
			pub fn start_signed_phase() {
				let targets = T::ElectionDataProvider::targets();
				let voters = T::ElectionDataProvider::voters();
				let desired_targets = T::ElectionDataProvider::desired_targets();
				<SnapshotTargets<T>>::put(targets);
				<SnapshotVoters<T>>::put(voters);
				DesiredTargets::put(desired_targets);
			}
			/// Finish the singed phase.
			///
			/// Returns true if we have a good solution in the signed phase.
			pub fn finalize_signed_phase() -> bool {
				let mut all_submission: Vec<SignedSubmission<_, _>> =
					<SignedSubmissions<T>>::take();
				let mut found_solution = false;
				while let Some(best) = all_submission.pop() {
					let SignedSubmission {
						solution,
						who,
						deposit,
						reward,
					} = best;
					match Self::feasibility_check(solution, ElectionCompute::Signed) {
						Ok(ready_solution) => {
							<QueuedSolution<T>>::put(ready_solution);
							let _remaining = T::Currency::unreserve(&who, deposit);
							if true {
								if !_remaining.is_zero() {
									{
										::std::rt::begin_panic(
											"assertion failed: _remaining.is_zero()",
										)
									}
								};
							};
							let positive_imbalance = T::Currency::deposit_creating(&who, reward);
							T::RewardHandler::on_unbalanced(positive_imbalance);
							found_solution = true;
							break;
						}
						Err(_) => {
							let (negative_imbalance, _remaining) =
								T::Currency::slash_reserved(&who, deposit);
							if true {
								if !_remaining.is_zero() {
									{
										::std::rt::begin_panic(
											"assertion failed: _remaining.is_zero()",
										)
									}
								};
							};
							T::SlashHandler::on_unbalanced(negative_imbalance);
						}
					}
				}
				all_submission.into_iter().for_each(|not_processed| {
					match &not_processed {
						tmp => {
							{
								::std::io::_eprint(::core::fmt::Arguments::new_v1_formatted(
									&["[", ":", "] ", " = ", "\n"],
									&match (
										&"frame/election-providers/src/two_phase/signed.rs",
										&65u32,
										&"&not_processed",
										&&tmp,
									) {
										(arg0, arg1, arg2, arg3) => [
											::core::fmt::ArgumentV1::new(
												arg0,
												::core::fmt::Display::fmt,
											),
											::core::fmt::ArgumentV1::new(
												arg1,
												::core::fmt::Display::fmt,
											),
											::core::fmt::ArgumentV1::new(
												arg2,
												::core::fmt::Display::fmt,
											),
											::core::fmt::ArgumentV1::new(
												arg3,
												::core::fmt::Debug::fmt,
											),
										],
									},
									&[
										::core::fmt::rt::v1::Argument {
											position: 0usize,
											format: ::core::fmt::rt::v1::FormatSpec {
												fill: ' ',
												align: ::core::fmt::rt::v1::Alignment::Unknown,
												flags: 0u32,
												precision: ::core::fmt::rt::v1::Count::Implied,
												width: ::core::fmt::rt::v1::Count::Implied,
											},
										},
										::core::fmt::rt::v1::Argument {
											position: 1usize,
											format: ::core::fmt::rt::v1::FormatSpec {
												fill: ' ',
												align: ::core::fmt::rt::v1::Alignment::Unknown,
												flags: 0u32,
												precision: ::core::fmt::rt::v1::Count::Implied,
												width: ::core::fmt::rt::v1::Count::Implied,
											},
										},
										::core::fmt::rt::v1::Argument {
											position: 2usize,
											format: ::core::fmt::rt::v1::FormatSpec {
												fill: ' ',
												align: ::core::fmt::rt::v1::Alignment::Unknown,
												flags: 0u32,
												precision: ::core::fmt::rt::v1::Count::Implied,
												width: ::core::fmt::rt::v1::Count::Implied,
											},
										},
										::core::fmt::rt::v1::Argument {
											position: 3usize,
											format: ::core::fmt::rt::v1::FormatSpec {
												fill: ' ',
												align: ::core::fmt::rt::v1::Alignment::Unknown,
												flags: 4u32,
												precision: ::core::fmt::rt::v1::Count::Implied,
												width: ::core::fmt::rt::v1::Count::Implied,
											},
										},
									],
								));
							};
							tmp
						}
					};
					let SignedSubmission { who, deposit, .. } = not_processed;
					let _remaining = T::Currency::unreserve(&who, deposit);
					if true {
						if !_remaining.is_zero() {
							{
								::std::rt::begin_panic("assertion failed: _remaining.is_zero()")
							}
						};
					};
				});
				found_solution
			}
			/// Find a proper position in the queue for the signed queue, whilst maintaining the order of
			/// solution quality.
			pub fn insert_submission(
				who: &T::AccountId,
				queue: &mut Vec<SignedSubmission<T::AccountId, BalanceOf<T>>>,
				solution: RawSolution,
			) -> Option<usize> {
				let outcome = queue
					.iter()
					.enumerate()
					.rev()
					.find_map(|(i, s)| {
						if is_score_better(
							solution.score,
							s.solution.score,
							T::SolutionImprovementThreshold::get(),
						) {
							Some(i + 1)
						} else {
							None
						}
					})
					.or(Some(0))
					.and_then(|at| {
						if at == 0 && queue.len() as u32 >= T::MaxSignedSubmissions::get() {
							None
						} else {
							let reward = Self::reward_for(&solution);
							let deposit = Self::deposit_for(&solution);
							let submission = SignedSubmission {
								who: who.clone(),
								deposit,
								reward,
								solution,
							};
							queue.insert(at, submission);
							if queue.len() as u32 > T::MaxSignedSubmissions::get() {
								queue.remove(0);
								Some(at - 1)
							} else {
								Some(at)
							}
						}
					});
				if true {
					if !(queue.len() as u32 <= T::MaxSignedSubmissions::get()) {
						{
							:: std :: rt :: begin_panic ( "assertion failed: queue.len() as u32 <= T::MaxSignedSubmissions::get()" )
						}
					};
				};
				outcome
			}
			pub fn deposit_for(solution: &RawSolution) -> BalanceOf<T> {
				let encoded_len: BalanceOf<T> = solution.using_encoded(|e| e.len() as u32).into();
				T::SignedDepositBase::get() + T::SignedDepositByte::get() * encoded_len
			}
			pub fn reward_for(solution: &RawSolution) -> BalanceOf<T> {
				T::SignedRewardBase::get()
					+ T::SignedRewardFactor::get()
						* solution.score[0].saturated_into::<BalanceOf<T>>()
			}
		}
	}
	pub mod unsigned {}
	type BalanceOf<T> =
		<<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;
	type PositiveImbalanceOf<T> = <<T as Trait>::Currency as Currency<
		<T as frame_system::Trait>::AccountId,
	>>::PositiveImbalance;
	type NegativeImbalanceOf<T> = <<T as Trait>::Currency as Currency<
		<T as frame_system::Trait>::AccountId,
	>>::NegativeImbalance;
	/// Accuracy used for on-chain election.
	pub type ChainAccuracy = Perbill;
	/// Accuracy used for off-chain election. This better be small.
	pub type OffchainAccuracy = PerU16;
	/// Data type used to index nominators in the compact type.
	pub type VoterIndex = u32;
	/// Data type used to index validators in the compact type.
	pub type TargetIndex = u16;
	#[allow(unknown_lints, eq_op)]
	const _: [(); 0 - !{
		const ASSERT: bool = size_of::<TargetIndex>() <= size_of::<usize>();
		ASSERT
	} as usize] = [];
	#[allow(unknown_lints, eq_op)]
	const _: [(); 0 - !{
		const ASSERT: bool = size_of::<VoterIndex>() <= size_of::<usize>();
		ASSERT
	} as usize] = [];
	#[allow(unknown_lints, eq_op)]
	const _: [(); 0 - !{
		const ASSERT: bool = size_of::<TargetIndex>() <= size_of::<u32>();
		ASSERT
	} as usize] = [];
	#[allow(unknown_lints, eq_op)]
	const _: [(); 0 - !{
		const ASSERT: bool = size_of::<VoterIndex>() <= size_of::<u32>();
		ASSERT
	} as usize] = [];
	extern crate sp_npos_elections as _npos;
	/// A struct to encode a election assignment in a compact way.
	impl _npos::codec::Encode for CompactAssignments {
		fn encode(&self) -> Vec<u8> {
			let mut r = ::alloc::vec::Vec::new();
			let votes1 = self
				.votes1
				.iter()
				.map(|(v, t)| {
					(
						_npos::codec::Compact(v.clone()),
						_npos::codec::Compact(t.clone()),
					)
				})
				.collect::<Vec<_>>();
			votes1.encode_to(&mut r);
			let votes2 = self
				.votes2
				.iter()
				.map(|(v, (t1, w), t2)| {
					(
						_npos::codec::Compact(v.clone()),
						(
							_npos::codec::Compact(t1.clone()),
							_npos::codec::Compact(w.clone()),
						),
						_npos::codec::Compact(t2.clone()),
					)
				})
				.collect::<Vec<_>>();
			votes2.encode_to(&mut r);
			let votes3 = self
				.votes3
				.iter()
				.map(|(v, inner, t_last)| {
					(
						_npos::codec::Compact(v.clone()),
						[
							(
								_npos::codec::Compact(inner[0usize].0.clone()),
								_npos::codec::Compact(inner[0usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[1usize].0.clone()),
								_npos::codec::Compact(inner[1usize].1.clone()),
							),
						],
						_npos::codec::Compact(t_last.clone()),
					)
				})
				.collect::<Vec<_>>();
			votes3.encode_to(&mut r);
			let votes4 = self
				.votes4
				.iter()
				.map(|(v, inner, t_last)| {
					(
						_npos::codec::Compact(v.clone()),
						[
							(
								_npos::codec::Compact(inner[0usize].0.clone()),
								_npos::codec::Compact(inner[0usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[1usize].0.clone()),
								_npos::codec::Compact(inner[1usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[2usize].0.clone()),
								_npos::codec::Compact(inner[2usize].1.clone()),
							),
						],
						_npos::codec::Compact(t_last.clone()),
					)
				})
				.collect::<Vec<_>>();
			votes4.encode_to(&mut r);
			let votes5 = self
				.votes5
				.iter()
				.map(|(v, inner, t_last)| {
					(
						_npos::codec::Compact(v.clone()),
						[
							(
								_npos::codec::Compact(inner[0usize].0.clone()),
								_npos::codec::Compact(inner[0usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[1usize].0.clone()),
								_npos::codec::Compact(inner[1usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[2usize].0.clone()),
								_npos::codec::Compact(inner[2usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[3usize].0.clone()),
								_npos::codec::Compact(inner[3usize].1.clone()),
							),
						],
						_npos::codec::Compact(t_last.clone()),
					)
				})
				.collect::<Vec<_>>();
			votes5.encode_to(&mut r);
			let votes6 = self
				.votes6
				.iter()
				.map(|(v, inner, t_last)| {
					(
						_npos::codec::Compact(v.clone()),
						[
							(
								_npos::codec::Compact(inner[0usize].0.clone()),
								_npos::codec::Compact(inner[0usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[1usize].0.clone()),
								_npos::codec::Compact(inner[1usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[2usize].0.clone()),
								_npos::codec::Compact(inner[2usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[3usize].0.clone()),
								_npos::codec::Compact(inner[3usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[4usize].0.clone()),
								_npos::codec::Compact(inner[4usize].1.clone()),
							),
						],
						_npos::codec::Compact(t_last.clone()),
					)
				})
				.collect::<Vec<_>>();
			votes6.encode_to(&mut r);
			let votes7 = self
				.votes7
				.iter()
				.map(|(v, inner, t_last)| {
					(
						_npos::codec::Compact(v.clone()),
						[
							(
								_npos::codec::Compact(inner[0usize].0.clone()),
								_npos::codec::Compact(inner[0usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[1usize].0.clone()),
								_npos::codec::Compact(inner[1usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[2usize].0.clone()),
								_npos::codec::Compact(inner[2usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[3usize].0.clone()),
								_npos::codec::Compact(inner[3usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[4usize].0.clone()),
								_npos::codec::Compact(inner[4usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[5usize].0.clone()),
								_npos::codec::Compact(inner[5usize].1.clone()),
							),
						],
						_npos::codec::Compact(t_last.clone()),
					)
				})
				.collect::<Vec<_>>();
			votes7.encode_to(&mut r);
			let votes8 = self
				.votes8
				.iter()
				.map(|(v, inner, t_last)| {
					(
						_npos::codec::Compact(v.clone()),
						[
							(
								_npos::codec::Compact(inner[0usize].0.clone()),
								_npos::codec::Compact(inner[0usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[1usize].0.clone()),
								_npos::codec::Compact(inner[1usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[2usize].0.clone()),
								_npos::codec::Compact(inner[2usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[3usize].0.clone()),
								_npos::codec::Compact(inner[3usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[4usize].0.clone()),
								_npos::codec::Compact(inner[4usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[5usize].0.clone()),
								_npos::codec::Compact(inner[5usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[6usize].0.clone()),
								_npos::codec::Compact(inner[6usize].1.clone()),
							),
						],
						_npos::codec::Compact(t_last.clone()),
					)
				})
				.collect::<Vec<_>>();
			votes8.encode_to(&mut r);
			let votes9 = self
				.votes9
				.iter()
				.map(|(v, inner, t_last)| {
					(
						_npos::codec::Compact(v.clone()),
						[
							(
								_npos::codec::Compact(inner[0usize].0.clone()),
								_npos::codec::Compact(inner[0usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[1usize].0.clone()),
								_npos::codec::Compact(inner[1usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[2usize].0.clone()),
								_npos::codec::Compact(inner[2usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[3usize].0.clone()),
								_npos::codec::Compact(inner[3usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[4usize].0.clone()),
								_npos::codec::Compact(inner[4usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[5usize].0.clone()),
								_npos::codec::Compact(inner[5usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[6usize].0.clone()),
								_npos::codec::Compact(inner[6usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[7usize].0.clone()),
								_npos::codec::Compact(inner[7usize].1.clone()),
							),
						],
						_npos::codec::Compact(t_last.clone()),
					)
				})
				.collect::<Vec<_>>();
			votes9.encode_to(&mut r);
			let votes10 = self
				.votes10
				.iter()
				.map(|(v, inner, t_last)| {
					(
						_npos::codec::Compact(v.clone()),
						[
							(
								_npos::codec::Compact(inner[0usize].0.clone()),
								_npos::codec::Compact(inner[0usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[1usize].0.clone()),
								_npos::codec::Compact(inner[1usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[2usize].0.clone()),
								_npos::codec::Compact(inner[2usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[3usize].0.clone()),
								_npos::codec::Compact(inner[3usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[4usize].0.clone()),
								_npos::codec::Compact(inner[4usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[5usize].0.clone()),
								_npos::codec::Compact(inner[5usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[6usize].0.clone()),
								_npos::codec::Compact(inner[6usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[7usize].0.clone()),
								_npos::codec::Compact(inner[7usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[8usize].0.clone()),
								_npos::codec::Compact(inner[8usize].1.clone()),
							),
						],
						_npos::codec::Compact(t_last.clone()),
					)
				})
				.collect::<Vec<_>>();
			votes10.encode_to(&mut r);
			let votes11 = self
				.votes11
				.iter()
				.map(|(v, inner, t_last)| {
					(
						_npos::codec::Compact(v.clone()),
						[
							(
								_npos::codec::Compact(inner[0usize].0.clone()),
								_npos::codec::Compact(inner[0usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[1usize].0.clone()),
								_npos::codec::Compact(inner[1usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[2usize].0.clone()),
								_npos::codec::Compact(inner[2usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[3usize].0.clone()),
								_npos::codec::Compact(inner[3usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[4usize].0.clone()),
								_npos::codec::Compact(inner[4usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[5usize].0.clone()),
								_npos::codec::Compact(inner[5usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[6usize].0.clone()),
								_npos::codec::Compact(inner[6usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[7usize].0.clone()),
								_npos::codec::Compact(inner[7usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[8usize].0.clone()),
								_npos::codec::Compact(inner[8usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[9usize].0.clone()),
								_npos::codec::Compact(inner[9usize].1.clone()),
							),
						],
						_npos::codec::Compact(t_last.clone()),
					)
				})
				.collect::<Vec<_>>();
			votes11.encode_to(&mut r);
			let votes12 = self
				.votes12
				.iter()
				.map(|(v, inner, t_last)| {
					(
						_npos::codec::Compact(v.clone()),
						[
							(
								_npos::codec::Compact(inner[0usize].0.clone()),
								_npos::codec::Compact(inner[0usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[1usize].0.clone()),
								_npos::codec::Compact(inner[1usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[2usize].0.clone()),
								_npos::codec::Compact(inner[2usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[3usize].0.clone()),
								_npos::codec::Compact(inner[3usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[4usize].0.clone()),
								_npos::codec::Compact(inner[4usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[5usize].0.clone()),
								_npos::codec::Compact(inner[5usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[6usize].0.clone()),
								_npos::codec::Compact(inner[6usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[7usize].0.clone()),
								_npos::codec::Compact(inner[7usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[8usize].0.clone()),
								_npos::codec::Compact(inner[8usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[9usize].0.clone()),
								_npos::codec::Compact(inner[9usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[10usize].0.clone()),
								_npos::codec::Compact(inner[10usize].1.clone()),
							),
						],
						_npos::codec::Compact(t_last.clone()),
					)
				})
				.collect::<Vec<_>>();
			votes12.encode_to(&mut r);
			let votes13 = self
				.votes13
				.iter()
				.map(|(v, inner, t_last)| {
					(
						_npos::codec::Compact(v.clone()),
						[
							(
								_npos::codec::Compact(inner[0usize].0.clone()),
								_npos::codec::Compact(inner[0usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[1usize].0.clone()),
								_npos::codec::Compact(inner[1usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[2usize].0.clone()),
								_npos::codec::Compact(inner[2usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[3usize].0.clone()),
								_npos::codec::Compact(inner[3usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[4usize].0.clone()),
								_npos::codec::Compact(inner[4usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[5usize].0.clone()),
								_npos::codec::Compact(inner[5usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[6usize].0.clone()),
								_npos::codec::Compact(inner[6usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[7usize].0.clone()),
								_npos::codec::Compact(inner[7usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[8usize].0.clone()),
								_npos::codec::Compact(inner[8usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[9usize].0.clone()),
								_npos::codec::Compact(inner[9usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[10usize].0.clone()),
								_npos::codec::Compact(inner[10usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[11usize].0.clone()),
								_npos::codec::Compact(inner[11usize].1.clone()),
							),
						],
						_npos::codec::Compact(t_last.clone()),
					)
				})
				.collect::<Vec<_>>();
			votes13.encode_to(&mut r);
			let votes14 = self
				.votes14
				.iter()
				.map(|(v, inner, t_last)| {
					(
						_npos::codec::Compact(v.clone()),
						[
							(
								_npos::codec::Compact(inner[0usize].0.clone()),
								_npos::codec::Compact(inner[0usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[1usize].0.clone()),
								_npos::codec::Compact(inner[1usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[2usize].0.clone()),
								_npos::codec::Compact(inner[2usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[3usize].0.clone()),
								_npos::codec::Compact(inner[3usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[4usize].0.clone()),
								_npos::codec::Compact(inner[4usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[5usize].0.clone()),
								_npos::codec::Compact(inner[5usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[6usize].0.clone()),
								_npos::codec::Compact(inner[6usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[7usize].0.clone()),
								_npos::codec::Compact(inner[7usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[8usize].0.clone()),
								_npos::codec::Compact(inner[8usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[9usize].0.clone()),
								_npos::codec::Compact(inner[9usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[10usize].0.clone()),
								_npos::codec::Compact(inner[10usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[11usize].0.clone()),
								_npos::codec::Compact(inner[11usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[12usize].0.clone()),
								_npos::codec::Compact(inner[12usize].1.clone()),
							),
						],
						_npos::codec::Compact(t_last.clone()),
					)
				})
				.collect::<Vec<_>>();
			votes14.encode_to(&mut r);
			let votes15 = self
				.votes15
				.iter()
				.map(|(v, inner, t_last)| {
					(
						_npos::codec::Compact(v.clone()),
						[
							(
								_npos::codec::Compact(inner[0usize].0.clone()),
								_npos::codec::Compact(inner[0usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[1usize].0.clone()),
								_npos::codec::Compact(inner[1usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[2usize].0.clone()),
								_npos::codec::Compact(inner[2usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[3usize].0.clone()),
								_npos::codec::Compact(inner[3usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[4usize].0.clone()),
								_npos::codec::Compact(inner[4usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[5usize].0.clone()),
								_npos::codec::Compact(inner[5usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[6usize].0.clone()),
								_npos::codec::Compact(inner[6usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[7usize].0.clone()),
								_npos::codec::Compact(inner[7usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[8usize].0.clone()),
								_npos::codec::Compact(inner[8usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[9usize].0.clone()),
								_npos::codec::Compact(inner[9usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[10usize].0.clone()),
								_npos::codec::Compact(inner[10usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[11usize].0.clone()),
								_npos::codec::Compact(inner[11usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[12usize].0.clone()),
								_npos::codec::Compact(inner[12usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[13usize].0.clone()),
								_npos::codec::Compact(inner[13usize].1.clone()),
							),
						],
						_npos::codec::Compact(t_last.clone()),
					)
				})
				.collect::<Vec<_>>();
			votes15.encode_to(&mut r);
			let votes16 = self
				.votes16
				.iter()
				.map(|(v, inner, t_last)| {
					(
						_npos::codec::Compact(v.clone()),
						[
							(
								_npos::codec::Compact(inner[0usize].0.clone()),
								_npos::codec::Compact(inner[0usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[1usize].0.clone()),
								_npos::codec::Compact(inner[1usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[2usize].0.clone()),
								_npos::codec::Compact(inner[2usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[3usize].0.clone()),
								_npos::codec::Compact(inner[3usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[4usize].0.clone()),
								_npos::codec::Compact(inner[4usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[5usize].0.clone()),
								_npos::codec::Compact(inner[5usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[6usize].0.clone()),
								_npos::codec::Compact(inner[6usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[7usize].0.clone()),
								_npos::codec::Compact(inner[7usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[8usize].0.clone()),
								_npos::codec::Compact(inner[8usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[9usize].0.clone()),
								_npos::codec::Compact(inner[9usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[10usize].0.clone()),
								_npos::codec::Compact(inner[10usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[11usize].0.clone()),
								_npos::codec::Compact(inner[11usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[12usize].0.clone()),
								_npos::codec::Compact(inner[12usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[13usize].0.clone()),
								_npos::codec::Compact(inner[13usize].1.clone()),
							),
							(
								_npos::codec::Compact(inner[14usize].0.clone()),
								_npos::codec::Compact(inner[14usize].1.clone()),
							),
						],
						_npos::codec::Compact(t_last.clone()),
					)
				})
				.collect::<Vec<_>>();
			votes16.encode_to(&mut r);
			r
		}
	}
	impl _npos::codec::Decode for CompactAssignments {
		fn decode<I: _npos::codec::Input>(value: &mut I) -> Result<Self, _npos::codec::Error> {
			let votes1 = <Vec<(
				_npos::codec::Compact<VoterIndex>,
				_npos::codec::Compact<TargetIndex>,
			)> as _npos::codec::Decode>::decode(value)?;
			let votes1 = votes1
				.into_iter()
				.map(|(v, t)| (v.0, t.0))
				.collect::<Vec<_>>();
			let votes2 = <Vec<(
				_npos::codec::Compact<VoterIndex>,
				(
					_npos::codec::Compact<TargetIndex>,
					_npos::codec::Compact<OffchainAccuracy>,
				),
				_npos::codec::Compact<TargetIndex>,
			)> as _npos::codec::Decode>::decode(value)?;
			let votes2 = votes2
				.into_iter()
				.map(|(v, (t1, w), t2)| (v.0, (t1.0, w.0), t2.0))
				.collect::<Vec<_>>();
			let votes3 = <Vec<(
				_npos::codec::Compact<VoterIndex>,
				[(
					_npos::codec::Compact<TargetIndex>,
					_npos::codec::Compact<OffchainAccuracy>,
				); 3usize - 1],
				_npos::codec::Compact<TargetIndex>,
			)> as _npos::codec::Decode>::decode(value)?;
			let votes3 = votes3
				.into_iter()
				.map(|(v, inner, t_last)| {
					(
						v.0,
						[
							((inner[0usize].0).0, (inner[0usize].1).0),
							((inner[1usize].0).0, (inner[1usize].1).0),
						],
						t_last.0,
					)
				})
				.collect::<Vec<_>>();
			let votes4 = <Vec<(
				_npos::codec::Compact<VoterIndex>,
				[(
					_npos::codec::Compact<TargetIndex>,
					_npos::codec::Compact<OffchainAccuracy>,
				); 4usize - 1],
				_npos::codec::Compact<TargetIndex>,
			)> as _npos::codec::Decode>::decode(value)?;
			let votes4 = votes4
				.into_iter()
				.map(|(v, inner, t_last)| {
					(
						v.0,
						[
							((inner[0usize].0).0, (inner[0usize].1).0),
							((inner[1usize].0).0, (inner[1usize].1).0),
							((inner[2usize].0).0, (inner[2usize].1).0),
						],
						t_last.0,
					)
				})
				.collect::<Vec<_>>();
			let votes5 = <Vec<(
				_npos::codec::Compact<VoterIndex>,
				[(
					_npos::codec::Compact<TargetIndex>,
					_npos::codec::Compact<OffchainAccuracy>,
				); 5usize - 1],
				_npos::codec::Compact<TargetIndex>,
			)> as _npos::codec::Decode>::decode(value)?;
			let votes5 = votes5
				.into_iter()
				.map(|(v, inner, t_last)| {
					(
						v.0,
						[
							((inner[0usize].0).0, (inner[0usize].1).0),
							((inner[1usize].0).0, (inner[1usize].1).0),
							((inner[2usize].0).0, (inner[2usize].1).0),
							((inner[3usize].0).0, (inner[3usize].1).0),
						],
						t_last.0,
					)
				})
				.collect::<Vec<_>>();
			let votes6 = <Vec<(
				_npos::codec::Compact<VoterIndex>,
				[(
					_npos::codec::Compact<TargetIndex>,
					_npos::codec::Compact<OffchainAccuracy>,
				); 6usize - 1],
				_npos::codec::Compact<TargetIndex>,
			)> as _npos::codec::Decode>::decode(value)?;
			let votes6 = votes6
				.into_iter()
				.map(|(v, inner, t_last)| {
					(
						v.0,
						[
							((inner[0usize].0).0, (inner[0usize].1).0),
							((inner[1usize].0).0, (inner[1usize].1).0),
							((inner[2usize].0).0, (inner[2usize].1).0),
							((inner[3usize].0).0, (inner[3usize].1).0),
							((inner[4usize].0).0, (inner[4usize].1).0),
						],
						t_last.0,
					)
				})
				.collect::<Vec<_>>();
			let votes7 = <Vec<(
				_npos::codec::Compact<VoterIndex>,
				[(
					_npos::codec::Compact<TargetIndex>,
					_npos::codec::Compact<OffchainAccuracy>,
				); 7usize - 1],
				_npos::codec::Compact<TargetIndex>,
			)> as _npos::codec::Decode>::decode(value)?;
			let votes7 = votes7
				.into_iter()
				.map(|(v, inner, t_last)| {
					(
						v.0,
						[
							((inner[0usize].0).0, (inner[0usize].1).0),
							((inner[1usize].0).0, (inner[1usize].1).0),
							((inner[2usize].0).0, (inner[2usize].1).0),
							((inner[3usize].0).0, (inner[3usize].1).0),
							((inner[4usize].0).0, (inner[4usize].1).0),
							((inner[5usize].0).0, (inner[5usize].1).0),
						],
						t_last.0,
					)
				})
				.collect::<Vec<_>>();
			let votes8 = <Vec<(
				_npos::codec::Compact<VoterIndex>,
				[(
					_npos::codec::Compact<TargetIndex>,
					_npos::codec::Compact<OffchainAccuracy>,
				); 8usize - 1],
				_npos::codec::Compact<TargetIndex>,
			)> as _npos::codec::Decode>::decode(value)?;
			let votes8 = votes8
				.into_iter()
				.map(|(v, inner, t_last)| {
					(
						v.0,
						[
							((inner[0usize].0).0, (inner[0usize].1).0),
							((inner[1usize].0).0, (inner[1usize].1).0),
							((inner[2usize].0).0, (inner[2usize].1).0),
							((inner[3usize].0).0, (inner[3usize].1).0),
							((inner[4usize].0).0, (inner[4usize].1).0),
							((inner[5usize].0).0, (inner[5usize].1).0),
							((inner[6usize].0).0, (inner[6usize].1).0),
						],
						t_last.0,
					)
				})
				.collect::<Vec<_>>();
			let votes9 = <Vec<(
				_npos::codec::Compact<VoterIndex>,
				[(
					_npos::codec::Compact<TargetIndex>,
					_npos::codec::Compact<OffchainAccuracy>,
				); 9usize - 1],
				_npos::codec::Compact<TargetIndex>,
			)> as _npos::codec::Decode>::decode(value)?;
			let votes9 = votes9
				.into_iter()
				.map(|(v, inner, t_last)| {
					(
						v.0,
						[
							((inner[0usize].0).0, (inner[0usize].1).0),
							((inner[1usize].0).0, (inner[1usize].1).0),
							((inner[2usize].0).0, (inner[2usize].1).0),
							((inner[3usize].0).0, (inner[3usize].1).0),
							((inner[4usize].0).0, (inner[4usize].1).0),
							((inner[5usize].0).0, (inner[5usize].1).0),
							((inner[6usize].0).0, (inner[6usize].1).0),
							((inner[7usize].0).0, (inner[7usize].1).0),
						],
						t_last.0,
					)
				})
				.collect::<Vec<_>>();
			let votes10 = <Vec<(
				_npos::codec::Compact<VoterIndex>,
				[(
					_npos::codec::Compact<TargetIndex>,
					_npos::codec::Compact<OffchainAccuracy>,
				); 10usize - 1],
				_npos::codec::Compact<TargetIndex>,
			)> as _npos::codec::Decode>::decode(value)?;
			let votes10 = votes10
				.into_iter()
				.map(|(v, inner, t_last)| {
					(
						v.0,
						[
							((inner[0usize].0).0, (inner[0usize].1).0),
							((inner[1usize].0).0, (inner[1usize].1).0),
							((inner[2usize].0).0, (inner[2usize].1).0),
							((inner[3usize].0).0, (inner[3usize].1).0),
							((inner[4usize].0).0, (inner[4usize].1).0),
							((inner[5usize].0).0, (inner[5usize].1).0),
							((inner[6usize].0).0, (inner[6usize].1).0),
							((inner[7usize].0).0, (inner[7usize].1).0),
							((inner[8usize].0).0, (inner[8usize].1).0),
						],
						t_last.0,
					)
				})
				.collect::<Vec<_>>();
			let votes11 = <Vec<(
				_npos::codec::Compact<VoterIndex>,
				[(
					_npos::codec::Compact<TargetIndex>,
					_npos::codec::Compact<OffchainAccuracy>,
				); 11usize - 1],
				_npos::codec::Compact<TargetIndex>,
			)> as _npos::codec::Decode>::decode(value)?;
			let votes11 = votes11
				.into_iter()
				.map(|(v, inner, t_last)| {
					(
						v.0,
						[
							((inner[0usize].0).0, (inner[0usize].1).0),
							((inner[1usize].0).0, (inner[1usize].1).0),
							((inner[2usize].0).0, (inner[2usize].1).0),
							((inner[3usize].0).0, (inner[3usize].1).0),
							((inner[4usize].0).0, (inner[4usize].1).0),
							((inner[5usize].0).0, (inner[5usize].1).0),
							((inner[6usize].0).0, (inner[6usize].1).0),
							((inner[7usize].0).0, (inner[7usize].1).0),
							((inner[8usize].0).0, (inner[8usize].1).0),
							((inner[9usize].0).0, (inner[9usize].1).0),
						],
						t_last.0,
					)
				})
				.collect::<Vec<_>>();
			let votes12 = <Vec<(
				_npos::codec::Compact<VoterIndex>,
				[(
					_npos::codec::Compact<TargetIndex>,
					_npos::codec::Compact<OffchainAccuracy>,
				); 12usize - 1],
				_npos::codec::Compact<TargetIndex>,
			)> as _npos::codec::Decode>::decode(value)?;
			let votes12 = votes12
				.into_iter()
				.map(|(v, inner, t_last)| {
					(
						v.0,
						[
							((inner[0usize].0).0, (inner[0usize].1).0),
							((inner[1usize].0).0, (inner[1usize].1).0),
							((inner[2usize].0).0, (inner[2usize].1).0),
							((inner[3usize].0).0, (inner[3usize].1).0),
							((inner[4usize].0).0, (inner[4usize].1).0),
							((inner[5usize].0).0, (inner[5usize].1).0),
							((inner[6usize].0).0, (inner[6usize].1).0),
							((inner[7usize].0).0, (inner[7usize].1).0),
							((inner[8usize].0).0, (inner[8usize].1).0),
							((inner[9usize].0).0, (inner[9usize].1).0),
							((inner[10usize].0).0, (inner[10usize].1).0),
						],
						t_last.0,
					)
				})
				.collect::<Vec<_>>();
			let votes13 = <Vec<(
				_npos::codec::Compact<VoterIndex>,
				[(
					_npos::codec::Compact<TargetIndex>,
					_npos::codec::Compact<OffchainAccuracy>,
				); 13usize - 1],
				_npos::codec::Compact<TargetIndex>,
			)> as _npos::codec::Decode>::decode(value)?;
			let votes13 = votes13
				.into_iter()
				.map(|(v, inner, t_last)| {
					(
						v.0,
						[
							((inner[0usize].0).0, (inner[0usize].1).0),
							((inner[1usize].0).0, (inner[1usize].1).0),
							((inner[2usize].0).0, (inner[2usize].1).0),
							((inner[3usize].0).0, (inner[3usize].1).0),
							((inner[4usize].0).0, (inner[4usize].1).0),
							((inner[5usize].0).0, (inner[5usize].1).0),
							((inner[6usize].0).0, (inner[6usize].1).0),
							((inner[7usize].0).0, (inner[7usize].1).0),
							((inner[8usize].0).0, (inner[8usize].1).0),
							((inner[9usize].0).0, (inner[9usize].1).0),
							((inner[10usize].0).0, (inner[10usize].1).0),
							((inner[11usize].0).0, (inner[11usize].1).0),
						],
						t_last.0,
					)
				})
				.collect::<Vec<_>>();
			let votes14 = <Vec<(
				_npos::codec::Compact<VoterIndex>,
				[(
					_npos::codec::Compact<TargetIndex>,
					_npos::codec::Compact<OffchainAccuracy>,
				); 14usize - 1],
				_npos::codec::Compact<TargetIndex>,
			)> as _npos::codec::Decode>::decode(value)?;
			let votes14 = votes14
				.into_iter()
				.map(|(v, inner, t_last)| {
					(
						v.0,
						[
							((inner[0usize].0).0, (inner[0usize].1).0),
							((inner[1usize].0).0, (inner[1usize].1).0),
							((inner[2usize].0).0, (inner[2usize].1).0),
							((inner[3usize].0).0, (inner[3usize].1).0),
							((inner[4usize].0).0, (inner[4usize].1).0),
							((inner[5usize].0).0, (inner[5usize].1).0),
							((inner[6usize].0).0, (inner[6usize].1).0),
							((inner[7usize].0).0, (inner[7usize].1).0),
							((inner[8usize].0).0, (inner[8usize].1).0),
							((inner[9usize].0).0, (inner[9usize].1).0),
							((inner[10usize].0).0, (inner[10usize].1).0),
							((inner[11usize].0).0, (inner[11usize].1).0),
							((inner[12usize].0).0, (inner[12usize].1).0),
						],
						t_last.0,
					)
				})
				.collect::<Vec<_>>();
			let votes15 = <Vec<(
				_npos::codec::Compact<VoterIndex>,
				[(
					_npos::codec::Compact<TargetIndex>,
					_npos::codec::Compact<OffchainAccuracy>,
				); 15usize - 1],
				_npos::codec::Compact<TargetIndex>,
			)> as _npos::codec::Decode>::decode(value)?;
			let votes15 = votes15
				.into_iter()
				.map(|(v, inner, t_last)| {
					(
						v.0,
						[
							((inner[0usize].0).0, (inner[0usize].1).0),
							((inner[1usize].0).0, (inner[1usize].1).0),
							((inner[2usize].0).0, (inner[2usize].1).0),
							((inner[3usize].0).0, (inner[3usize].1).0),
							((inner[4usize].0).0, (inner[4usize].1).0),
							((inner[5usize].0).0, (inner[5usize].1).0),
							((inner[6usize].0).0, (inner[6usize].1).0),
							((inner[7usize].0).0, (inner[7usize].1).0),
							((inner[8usize].0).0, (inner[8usize].1).0),
							((inner[9usize].0).0, (inner[9usize].1).0),
							((inner[10usize].0).0, (inner[10usize].1).0),
							((inner[11usize].0).0, (inner[11usize].1).0),
							((inner[12usize].0).0, (inner[12usize].1).0),
							((inner[13usize].0).0, (inner[13usize].1).0),
						],
						t_last.0,
					)
				})
				.collect::<Vec<_>>();
			let votes16 = <Vec<(
				_npos::codec::Compact<VoterIndex>,
				[(
					_npos::codec::Compact<TargetIndex>,
					_npos::codec::Compact<OffchainAccuracy>,
				); 16usize - 1],
				_npos::codec::Compact<TargetIndex>,
			)> as _npos::codec::Decode>::decode(value)?;
			let votes16 = votes16
				.into_iter()
				.map(|(v, inner, t_last)| {
					(
						v.0,
						[
							((inner[0usize].0).0, (inner[0usize].1).0),
							((inner[1usize].0).0, (inner[1usize].1).0),
							((inner[2usize].0).0, (inner[2usize].1).0),
							((inner[3usize].0).0, (inner[3usize].1).0),
							((inner[4usize].0).0, (inner[4usize].1).0),
							((inner[5usize].0).0, (inner[5usize].1).0),
							((inner[6usize].0).0, (inner[6usize].1).0),
							((inner[7usize].0).0, (inner[7usize].1).0),
							((inner[8usize].0).0, (inner[8usize].1).0),
							((inner[9usize].0).0, (inner[9usize].1).0),
							((inner[10usize].0).0, (inner[10usize].1).0),
							((inner[11usize].0).0, (inner[11usize].1).0),
							((inner[12usize].0).0, (inner[12usize].1).0),
							((inner[13usize].0).0, (inner[13usize].1).0),
							((inner[14usize].0).0, (inner[14usize].1).0),
						],
						t_last.0,
					)
				})
				.collect::<Vec<_>>();
			Ok(CompactAssignments {
				votes1,
				votes2,
				votes3,
				votes4,
				votes5,
				votes6,
				votes7,
				votes8,
				votes9,
				votes10,
				votes11,
				votes12,
				votes13,
				votes14,
				votes15,
				votes16,
			})
		}
	}
	pub struct CompactAssignments {
		votes1: Vec<(VoterIndex, TargetIndex)>,
		votes2: Vec<(VoterIndex, (TargetIndex, OffchainAccuracy), TargetIndex)>,
		votes3: Vec<(
			VoterIndex,
			[(TargetIndex, OffchainAccuracy); 2usize],
			TargetIndex,
		)>,
		votes4: Vec<(
			VoterIndex,
			[(TargetIndex, OffchainAccuracy); 3usize],
			TargetIndex,
		)>,
		votes5: Vec<(
			VoterIndex,
			[(TargetIndex, OffchainAccuracy); 4usize],
			TargetIndex,
		)>,
		votes6: Vec<(
			VoterIndex,
			[(TargetIndex, OffchainAccuracy); 5usize],
			TargetIndex,
		)>,
		votes7: Vec<(
			VoterIndex,
			[(TargetIndex, OffchainAccuracy); 6usize],
			TargetIndex,
		)>,
		votes8: Vec<(
			VoterIndex,
			[(TargetIndex, OffchainAccuracy); 7usize],
			TargetIndex,
		)>,
		votes9: Vec<(
			VoterIndex,
			[(TargetIndex, OffchainAccuracy); 8usize],
			TargetIndex,
		)>,
		votes10: Vec<(
			VoterIndex,
			[(TargetIndex, OffchainAccuracy); 9usize],
			TargetIndex,
		)>,
		votes11: Vec<(
			VoterIndex,
			[(TargetIndex, OffchainAccuracy); 10usize],
			TargetIndex,
		)>,
		votes12: Vec<(
			VoterIndex,
			[(TargetIndex, OffchainAccuracy); 11usize],
			TargetIndex,
		)>,
		votes13: Vec<(
			VoterIndex,
			[(TargetIndex, OffchainAccuracy); 12usize],
			TargetIndex,
		)>,
		votes14: Vec<(
			VoterIndex,
			[(TargetIndex, OffchainAccuracy); 13usize],
			TargetIndex,
		)>,
		votes15: Vec<(
			VoterIndex,
			[(TargetIndex, OffchainAccuracy); 14usize],
			TargetIndex,
		)>,
		votes16: Vec<(
			VoterIndex,
			[(TargetIndex, OffchainAccuracy); 15usize],
			TargetIndex,
		)>,
	}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl ::core::default::Default for CompactAssignments {
		#[inline]
		fn default() -> CompactAssignments {
			CompactAssignments {
				votes1: ::core::default::Default::default(),
				votes2: ::core::default::Default::default(),
				votes3: ::core::default::Default::default(),
				votes4: ::core::default::Default::default(),
				votes5: ::core::default::Default::default(),
				votes6: ::core::default::Default::default(),
				votes7: ::core::default::Default::default(),
				votes8: ::core::default::Default::default(),
				votes9: ::core::default::Default::default(),
				votes10: ::core::default::Default::default(),
				votes11: ::core::default::Default::default(),
				votes12: ::core::default::Default::default(),
				votes13: ::core::default::Default::default(),
				votes14: ::core::default::Default::default(),
				votes15: ::core::default::Default::default(),
				votes16: ::core::default::Default::default(),
			}
		}
	}
	impl ::core::marker::StructuralPartialEq for CompactAssignments {}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl ::core::cmp::PartialEq for CompactAssignments {
		#[inline]
		fn eq(&self, other: &CompactAssignments) -> bool {
			match *other {
				CompactAssignments {
					votes1: ref __self_1_0,
					votes2: ref __self_1_1,
					votes3: ref __self_1_2,
					votes4: ref __self_1_3,
					votes5: ref __self_1_4,
					votes6: ref __self_1_5,
					votes7: ref __self_1_6,
					votes8: ref __self_1_7,
					votes9: ref __self_1_8,
					votes10: ref __self_1_9,
					votes11: ref __self_1_10,
					votes12: ref __self_1_11,
					votes13: ref __self_1_12,
					votes14: ref __self_1_13,
					votes15: ref __self_1_14,
					votes16: ref __self_1_15,
				} => match *self {
					CompactAssignments {
						votes1: ref __self_0_0,
						votes2: ref __self_0_1,
						votes3: ref __self_0_2,
						votes4: ref __self_0_3,
						votes5: ref __self_0_4,
						votes6: ref __self_0_5,
						votes7: ref __self_0_6,
						votes8: ref __self_0_7,
						votes9: ref __self_0_8,
						votes10: ref __self_0_9,
						votes11: ref __self_0_10,
						votes12: ref __self_0_11,
						votes13: ref __self_0_12,
						votes14: ref __self_0_13,
						votes15: ref __self_0_14,
						votes16: ref __self_0_15,
					} => {
						(*__self_0_0) == (*__self_1_0)
							&& (*__self_0_1) == (*__self_1_1)
							&& (*__self_0_2) == (*__self_1_2)
							&& (*__self_0_3) == (*__self_1_3)
							&& (*__self_0_4) == (*__self_1_4)
							&& (*__self_0_5) == (*__self_1_5)
							&& (*__self_0_6) == (*__self_1_6)
							&& (*__self_0_7) == (*__self_1_7)
							&& (*__self_0_8) == (*__self_1_8)
							&& (*__self_0_9) == (*__self_1_9)
							&& (*__self_0_10) == (*__self_1_10)
							&& (*__self_0_11) == (*__self_1_11)
							&& (*__self_0_12) == (*__self_1_12)
							&& (*__self_0_13) == (*__self_1_13)
							&& (*__self_0_14) == (*__self_1_14)
							&& (*__self_0_15) == (*__self_1_15)
					}
				},
			}
		}
		#[inline]
		fn ne(&self, other: &CompactAssignments) -> bool {
			match *other {
				CompactAssignments {
					votes1: ref __self_1_0,
					votes2: ref __self_1_1,
					votes3: ref __self_1_2,
					votes4: ref __self_1_3,
					votes5: ref __self_1_4,
					votes6: ref __self_1_5,
					votes7: ref __self_1_6,
					votes8: ref __self_1_7,
					votes9: ref __self_1_8,
					votes10: ref __self_1_9,
					votes11: ref __self_1_10,
					votes12: ref __self_1_11,
					votes13: ref __self_1_12,
					votes14: ref __self_1_13,
					votes15: ref __self_1_14,
					votes16: ref __self_1_15,
				} => match *self {
					CompactAssignments {
						votes1: ref __self_0_0,
						votes2: ref __self_0_1,
						votes3: ref __self_0_2,
						votes4: ref __self_0_3,
						votes5: ref __self_0_4,
						votes6: ref __self_0_5,
						votes7: ref __self_0_6,
						votes8: ref __self_0_7,
						votes9: ref __self_0_8,
						votes10: ref __self_0_9,
						votes11: ref __self_0_10,
						votes12: ref __self_0_11,
						votes13: ref __self_0_12,
						votes14: ref __self_0_13,
						votes15: ref __self_0_14,
						votes16: ref __self_0_15,
					} => {
						(*__self_0_0) != (*__self_1_0)
							|| (*__self_0_1) != (*__self_1_1)
							|| (*__self_0_2) != (*__self_1_2)
							|| (*__self_0_3) != (*__self_1_3)
							|| (*__self_0_4) != (*__self_1_4)
							|| (*__self_0_5) != (*__self_1_5)
							|| (*__self_0_6) != (*__self_1_6)
							|| (*__self_0_7) != (*__self_1_7)
							|| (*__self_0_8) != (*__self_1_8)
							|| (*__self_0_9) != (*__self_1_9)
							|| (*__self_0_10) != (*__self_1_10)
							|| (*__self_0_11) != (*__self_1_11)
							|| (*__self_0_12) != (*__self_1_12)
							|| (*__self_0_13) != (*__self_1_13)
							|| (*__self_0_14) != (*__self_1_14)
							|| (*__self_0_15) != (*__self_1_15)
					}
				},
			}
		}
	}
	impl ::core::marker::StructuralEq for CompactAssignments {}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl ::core::cmp::Eq for CompactAssignments {
		#[inline]
		#[doc(hidden)]
		fn assert_receiver_is_total_eq(&self) -> () {
			{
				let _: ::core::cmp::AssertParamIsEq<Vec<(VoterIndex, TargetIndex)>>;
				let _: ::core::cmp::AssertParamIsEq<
					Vec<(VoterIndex, (TargetIndex, OffchainAccuracy), TargetIndex)>,
				>;
				let _: ::core::cmp::AssertParamIsEq<
					Vec<(
						VoterIndex,
						[(TargetIndex, OffchainAccuracy); 2usize],
						TargetIndex,
					)>,
				>;
				let _: ::core::cmp::AssertParamIsEq<
					Vec<(
						VoterIndex,
						[(TargetIndex, OffchainAccuracy); 3usize],
						TargetIndex,
					)>,
				>;
				let _: ::core::cmp::AssertParamIsEq<
					Vec<(
						VoterIndex,
						[(TargetIndex, OffchainAccuracy); 4usize],
						TargetIndex,
					)>,
				>;
				let _: ::core::cmp::AssertParamIsEq<
					Vec<(
						VoterIndex,
						[(TargetIndex, OffchainAccuracy); 5usize],
						TargetIndex,
					)>,
				>;
				let _: ::core::cmp::AssertParamIsEq<
					Vec<(
						VoterIndex,
						[(TargetIndex, OffchainAccuracy); 6usize],
						TargetIndex,
					)>,
				>;
				let _: ::core::cmp::AssertParamIsEq<
					Vec<(
						VoterIndex,
						[(TargetIndex, OffchainAccuracy); 7usize],
						TargetIndex,
					)>,
				>;
				let _: ::core::cmp::AssertParamIsEq<
					Vec<(
						VoterIndex,
						[(TargetIndex, OffchainAccuracy); 8usize],
						TargetIndex,
					)>,
				>;
				let _: ::core::cmp::AssertParamIsEq<
					Vec<(
						VoterIndex,
						[(TargetIndex, OffchainAccuracy); 9usize],
						TargetIndex,
					)>,
				>;
				let _: ::core::cmp::AssertParamIsEq<
					Vec<(
						VoterIndex,
						[(TargetIndex, OffchainAccuracy); 10usize],
						TargetIndex,
					)>,
				>;
				let _: ::core::cmp::AssertParamIsEq<
					Vec<(
						VoterIndex,
						[(TargetIndex, OffchainAccuracy); 11usize],
						TargetIndex,
					)>,
				>;
				let _: ::core::cmp::AssertParamIsEq<
					Vec<(
						VoterIndex,
						[(TargetIndex, OffchainAccuracy); 12usize],
						TargetIndex,
					)>,
				>;
				let _: ::core::cmp::AssertParamIsEq<
					Vec<(
						VoterIndex,
						[(TargetIndex, OffchainAccuracy); 13usize],
						TargetIndex,
					)>,
				>;
				let _: ::core::cmp::AssertParamIsEq<
					Vec<(
						VoterIndex,
						[(TargetIndex, OffchainAccuracy); 14usize],
						TargetIndex,
					)>,
				>;
				let _: ::core::cmp::AssertParamIsEq<
					Vec<(
						VoterIndex,
						[(TargetIndex, OffchainAccuracy); 15usize],
						TargetIndex,
					)>,
				>;
			}
		}
	}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl ::core::clone::Clone for CompactAssignments {
		#[inline]
		fn clone(&self) -> CompactAssignments {
			match *self {
				CompactAssignments {
					votes1: ref __self_0_0,
					votes2: ref __self_0_1,
					votes3: ref __self_0_2,
					votes4: ref __self_0_3,
					votes5: ref __self_0_4,
					votes6: ref __self_0_5,
					votes7: ref __self_0_6,
					votes8: ref __self_0_7,
					votes9: ref __self_0_8,
					votes10: ref __self_0_9,
					votes11: ref __self_0_10,
					votes12: ref __self_0_11,
					votes13: ref __self_0_12,
					votes14: ref __self_0_13,
					votes15: ref __self_0_14,
					votes16: ref __self_0_15,
				} => CompactAssignments {
					votes1: ::core::clone::Clone::clone(&(*__self_0_0)),
					votes2: ::core::clone::Clone::clone(&(*__self_0_1)),
					votes3: ::core::clone::Clone::clone(&(*__self_0_2)),
					votes4: ::core::clone::Clone::clone(&(*__self_0_3)),
					votes5: ::core::clone::Clone::clone(&(*__self_0_4)),
					votes6: ::core::clone::Clone::clone(&(*__self_0_5)),
					votes7: ::core::clone::Clone::clone(&(*__self_0_6)),
					votes8: ::core::clone::Clone::clone(&(*__self_0_7)),
					votes9: ::core::clone::Clone::clone(&(*__self_0_8)),
					votes10: ::core::clone::Clone::clone(&(*__self_0_9)),
					votes11: ::core::clone::Clone::clone(&(*__self_0_10)),
					votes12: ::core::clone::Clone::clone(&(*__self_0_11)),
					votes13: ::core::clone::Clone::clone(&(*__self_0_12)),
					votes14: ::core::clone::Clone::clone(&(*__self_0_13)),
					votes15: ::core::clone::Clone::clone(&(*__self_0_14)),
					votes16: ::core::clone::Clone::clone(&(*__self_0_15)),
				},
			}
		}
	}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl ::core::fmt::Debug for CompactAssignments {
		fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
			match *self {
				CompactAssignments {
					votes1: ref __self_0_0,
					votes2: ref __self_0_1,
					votes3: ref __self_0_2,
					votes4: ref __self_0_3,
					votes5: ref __self_0_4,
					votes6: ref __self_0_5,
					votes7: ref __self_0_6,
					votes8: ref __self_0_7,
					votes9: ref __self_0_8,
					votes10: ref __self_0_9,
					votes11: ref __self_0_10,
					votes12: ref __self_0_11,
					votes13: ref __self_0_12,
					votes14: ref __self_0_13,
					votes15: ref __self_0_14,
					votes16: ref __self_0_15,
				} => {
					let mut debug_trait_builder = f.debug_struct("CompactAssignments");
					let _ = debug_trait_builder.field("votes1", &&(*__self_0_0));
					let _ = debug_trait_builder.field("votes2", &&(*__self_0_1));
					let _ = debug_trait_builder.field("votes3", &&(*__self_0_2));
					let _ = debug_trait_builder.field("votes4", &&(*__self_0_3));
					let _ = debug_trait_builder.field("votes5", &&(*__self_0_4));
					let _ = debug_trait_builder.field("votes6", &&(*__self_0_5));
					let _ = debug_trait_builder.field("votes7", &&(*__self_0_6));
					let _ = debug_trait_builder.field("votes8", &&(*__self_0_7));
					let _ = debug_trait_builder.field("votes9", &&(*__self_0_8));
					let _ = debug_trait_builder.field("votes10", &&(*__self_0_9));
					let _ = debug_trait_builder.field("votes11", &&(*__self_0_10));
					let _ = debug_trait_builder.field("votes12", &&(*__self_0_11));
					let _ = debug_trait_builder.field("votes13", &&(*__self_0_12));
					let _ = debug_trait_builder.field("votes14", &&(*__self_0_13));
					let _ = debug_trait_builder.field("votes15", &&(*__self_0_14));
					let _ = debug_trait_builder.field("votes16", &&(*__self_0_15));
					debug_trait_builder.finish()
				}
			}
		}
	}
	impl _npos::VotingLimit for CompactAssignments {
		const LIMIT: usize = 16usize;
	}
	impl CompactAssignments {
		/// Get the length of all the assignments that this type is encoding. This is basically
		/// the same as the number of assignments, or the number of voters in total.
		pub fn len(&self) -> usize {
			let mut all_len = 0usize;
			all_len = all_len.saturating_add(self.votes1.len());
			all_len = all_len.saturating_add(self.votes2.len());
			all_len = all_len.saturating_add(self.votes3.len());
			all_len = all_len.saturating_add(self.votes4.len());
			all_len = all_len.saturating_add(self.votes5.len());
			all_len = all_len.saturating_add(self.votes6.len());
			all_len = all_len.saturating_add(self.votes7.len());
			all_len = all_len.saturating_add(self.votes8.len());
			all_len = all_len.saturating_add(self.votes9.len());
			all_len = all_len.saturating_add(self.votes10.len());
			all_len = all_len.saturating_add(self.votes11.len());
			all_len = all_len.saturating_add(self.votes12.len());
			all_len = all_len.saturating_add(self.votes13.len());
			all_len = all_len.saturating_add(self.votes14.len());
			all_len = all_len.saturating_add(self.votes15.len());
			all_len = all_len.saturating_add(self.votes16.len());
			all_len
		}
		/// Get the total count of edges.
		pub fn edge_count(&self) -> usize {
			let mut all_edges = 0usize;
			all_edges = all_edges.saturating_add(self.votes1.len().saturating_mul(1usize as usize));
			all_edges = all_edges.saturating_add(self.votes2.len().saturating_mul(2usize as usize));
			all_edges = all_edges.saturating_add(self.votes3.len().saturating_mul(3usize as usize));
			all_edges = all_edges.saturating_add(self.votes4.len().saturating_mul(4usize as usize));
			all_edges = all_edges.saturating_add(self.votes5.len().saturating_mul(5usize as usize));
			all_edges = all_edges.saturating_add(self.votes6.len().saturating_mul(6usize as usize));
			all_edges = all_edges.saturating_add(self.votes7.len().saturating_mul(7usize as usize));
			all_edges = all_edges.saturating_add(self.votes8.len().saturating_mul(8usize as usize));
			all_edges = all_edges.saturating_add(self.votes9.len().saturating_mul(9usize as usize));
			all_edges =
				all_edges.saturating_add(self.votes10.len().saturating_mul(10usize as usize));
			all_edges =
				all_edges.saturating_add(self.votes11.len().saturating_mul(11usize as usize));
			all_edges =
				all_edges.saturating_add(self.votes12.len().saturating_mul(12usize as usize));
			all_edges =
				all_edges.saturating_add(self.votes13.len().saturating_mul(13usize as usize));
			all_edges =
				all_edges.saturating_add(self.votes14.len().saturating_mul(14usize as usize));
			all_edges =
				all_edges.saturating_add(self.votes15.len().saturating_mul(15usize as usize));
			all_edges =
				all_edges.saturating_add(self.votes16.len().saturating_mul(16usize as usize));
			all_edges
		}
		/// Get the number of unique targets in the whole struct.
		///
		/// Once presented with a list of winners, this set and the set of winners must be
		/// equal.
		///
		/// The resulting indices are sorted.
		pub fn unique_targets(&self) -> Vec<TargetIndex> {
			let mut all_targets: Vec<TargetIndex> = Vec::with_capacity(self.average_edge_count());
			let mut maybe_insert_target = |t: TargetIndex| match all_targets.binary_search(&t) {
				Ok(_) => (),
				Err(pos) => all_targets.insert(pos, t),
			};
			self.votes1.iter().for_each(|(_, t)| {
				maybe_insert_target(*t);
			});
			self.votes2.iter().for_each(|(_, (t1, _), t2)| {
				maybe_insert_target(*t1);
				maybe_insert_target(*t2);
			});
			self.votes3.iter().for_each(|(_, inners, t_last)| {
				inners.iter().for_each(|(t, _)| {
					maybe_insert_target(*t);
				});
				maybe_insert_target(*t_last);
			});
			self.votes4.iter().for_each(|(_, inners, t_last)| {
				inners.iter().for_each(|(t, _)| {
					maybe_insert_target(*t);
				});
				maybe_insert_target(*t_last);
			});
			self.votes5.iter().for_each(|(_, inners, t_last)| {
				inners.iter().for_each(|(t, _)| {
					maybe_insert_target(*t);
				});
				maybe_insert_target(*t_last);
			});
			self.votes6.iter().for_each(|(_, inners, t_last)| {
				inners.iter().for_each(|(t, _)| {
					maybe_insert_target(*t);
				});
				maybe_insert_target(*t_last);
			});
			self.votes7.iter().for_each(|(_, inners, t_last)| {
				inners.iter().for_each(|(t, _)| {
					maybe_insert_target(*t);
				});
				maybe_insert_target(*t_last);
			});
			self.votes8.iter().for_each(|(_, inners, t_last)| {
				inners.iter().for_each(|(t, _)| {
					maybe_insert_target(*t);
				});
				maybe_insert_target(*t_last);
			});
			self.votes9.iter().for_each(|(_, inners, t_last)| {
				inners.iter().for_each(|(t, _)| {
					maybe_insert_target(*t);
				});
				maybe_insert_target(*t_last);
			});
			self.votes10.iter().for_each(|(_, inners, t_last)| {
				inners.iter().for_each(|(t, _)| {
					maybe_insert_target(*t);
				});
				maybe_insert_target(*t_last);
			});
			self.votes11.iter().for_each(|(_, inners, t_last)| {
				inners.iter().for_each(|(t, _)| {
					maybe_insert_target(*t);
				});
				maybe_insert_target(*t_last);
			});
			self.votes12.iter().for_each(|(_, inners, t_last)| {
				inners.iter().for_each(|(t, _)| {
					maybe_insert_target(*t);
				});
				maybe_insert_target(*t_last);
			});
			self.votes13.iter().for_each(|(_, inners, t_last)| {
				inners.iter().for_each(|(t, _)| {
					maybe_insert_target(*t);
				});
				maybe_insert_target(*t_last);
			});
			self.votes14.iter().for_each(|(_, inners, t_last)| {
				inners.iter().for_each(|(t, _)| {
					maybe_insert_target(*t);
				});
				maybe_insert_target(*t_last);
			});
			self.votes15.iter().for_each(|(_, inners, t_last)| {
				inners.iter().for_each(|(t, _)| {
					maybe_insert_target(*t);
				});
				maybe_insert_target(*t_last);
			});
			self.votes16.iter().for_each(|(_, inners, t_last)| {
				inners.iter().for_each(|(t, _)| {
					maybe_insert_target(*t);
				});
				maybe_insert_target(*t_last);
			});
			all_targets
		}
		/// Get the average edge count.
		pub fn average_edge_count(&self) -> usize {
			self.edge_count().checked_div(self.len()).unwrap_or(0)
		}
		/// Remove a certain voter.
		///
		/// This will only search until the first instance of `to_remove`, and return true. If
		/// no instance is found (no-op), then it returns false.
		///
		/// In other words, if this return true, exactly one element must have been removed from
		/// `self.len()`.
		pub fn remove_voter(&mut self, to_remove: VoterIndex) -> bool {
			if let Some(idx) = self.votes1.iter().position(|(x, _)| *x == to_remove) {
				self.votes1.remove(idx);
				return true;
			}
			if let Some(idx) = self.votes2.iter().position(|(x, _, _)| *x == to_remove) {
				self.votes2.remove(idx);
				return true;
			}
			if let Some(idx) = self.votes3.iter().position(|(x, _, _)| *x == to_remove) {
				self.votes3.remove(idx);
				return true;
			}
			if let Some(idx) = self.votes4.iter().position(|(x, _, _)| *x == to_remove) {
				self.votes4.remove(idx);
				return true;
			}
			if let Some(idx) = self.votes5.iter().position(|(x, _, _)| *x == to_remove) {
				self.votes5.remove(idx);
				return true;
			}
			if let Some(idx) = self.votes6.iter().position(|(x, _, _)| *x == to_remove) {
				self.votes6.remove(idx);
				return true;
			}
			if let Some(idx) = self.votes7.iter().position(|(x, _, _)| *x == to_remove) {
				self.votes7.remove(idx);
				return true;
			}
			if let Some(idx) = self.votes8.iter().position(|(x, _, _)| *x == to_remove) {
				self.votes8.remove(idx);
				return true;
			}
			if let Some(idx) = self.votes9.iter().position(|(x, _, _)| *x == to_remove) {
				self.votes9.remove(idx);
				return true;
			}
			if let Some(idx) = self.votes10.iter().position(|(x, _, _)| *x == to_remove) {
				self.votes10.remove(idx);
				return true;
			}
			if let Some(idx) = self.votes11.iter().position(|(x, _, _)| *x == to_remove) {
				self.votes11.remove(idx);
				return true;
			}
			if let Some(idx) = self.votes12.iter().position(|(x, _, _)| *x == to_remove) {
				self.votes12.remove(idx);
				return true;
			}
			if let Some(idx) = self.votes13.iter().position(|(x, _, _)| *x == to_remove) {
				self.votes13.remove(idx);
				return true;
			}
			if let Some(idx) = self.votes14.iter().position(|(x, _, _)| *x == to_remove) {
				self.votes14.remove(idx);
				return true;
			}
			if let Some(idx) = self.votes15.iter().position(|(x, _, _)| *x == to_remove) {
				self.votes15.remove(idx);
				return true;
			}
			if let Some(idx) = self.votes16.iter().position(|(x, _, _)| *x == to_remove) {
				self.votes16.remove(idx);
				return true;
			}
			return false;
		}
	}
	use _npos::__OrInvalidIndex;
	impl CompactAssignments {
		pub fn from_assignment<FV, FT, A>(
			assignments: Vec<_npos::Assignment<A, OffchainAccuracy>>,
			index_of_voter: FV,
			index_of_target: FT,
		) -> Result<Self, _npos::Error>
		where
			A: _npos::IdentifierT,
			for<'r> FV: Fn(&'r A) -> Option<VoterIndex>,
			for<'r> FT: Fn(&'r A) -> Option<TargetIndex>,
		{
			let mut compact: CompactAssignments = Default::default();
			for _npos::Assignment { who, distribution } in assignments {
				match distribution.len() {
					0 => continue,
					1 => compact.votes1.push((
						index_of_voter(&who).or_invalid_index()?,
						index_of_target(&distribution[0].0).or_invalid_index()?,
					)),
					2 => compact.votes2.push((
						index_of_voter(&who).or_invalid_index()?,
						(
							index_of_target(&distribution[0].0).or_invalid_index()?,
							distribution[0].1,
						),
						index_of_target(&distribution[1].0).or_invalid_index()?,
					)),
					3usize => compact.votes3.push((
						index_of_voter(&who).or_invalid_index()?,
						[
							(
								index_of_target(&distribution[0usize].0).or_invalid_index()?,
								distribution[0usize].1,
							),
							(
								index_of_target(&distribution[1usize].0).or_invalid_index()?,
								distribution[1usize].1,
							),
						],
						index_of_target(&distribution[2usize].0).or_invalid_index()?,
					)),
					4usize => compact.votes4.push((
						index_of_voter(&who).or_invalid_index()?,
						[
							(
								index_of_target(&distribution[0usize].0).or_invalid_index()?,
								distribution[0usize].1,
							),
							(
								index_of_target(&distribution[1usize].0).or_invalid_index()?,
								distribution[1usize].1,
							),
							(
								index_of_target(&distribution[2usize].0).or_invalid_index()?,
								distribution[2usize].1,
							),
						],
						index_of_target(&distribution[3usize].0).or_invalid_index()?,
					)),
					5usize => compact.votes5.push((
						index_of_voter(&who).or_invalid_index()?,
						[
							(
								index_of_target(&distribution[0usize].0).or_invalid_index()?,
								distribution[0usize].1,
							),
							(
								index_of_target(&distribution[1usize].0).or_invalid_index()?,
								distribution[1usize].1,
							),
							(
								index_of_target(&distribution[2usize].0).or_invalid_index()?,
								distribution[2usize].1,
							),
							(
								index_of_target(&distribution[3usize].0).or_invalid_index()?,
								distribution[3usize].1,
							),
						],
						index_of_target(&distribution[4usize].0).or_invalid_index()?,
					)),
					6usize => compact.votes6.push((
						index_of_voter(&who).or_invalid_index()?,
						[
							(
								index_of_target(&distribution[0usize].0).or_invalid_index()?,
								distribution[0usize].1,
							),
							(
								index_of_target(&distribution[1usize].0).or_invalid_index()?,
								distribution[1usize].1,
							),
							(
								index_of_target(&distribution[2usize].0).or_invalid_index()?,
								distribution[2usize].1,
							),
							(
								index_of_target(&distribution[3usize].0).or_invalid_index()?,
								distribution[3usize].1,
							),
							(
								index_of_target(&distribution[4usize].0).or_invalid_index()?,
								distribution[4usize].1,
							),
						],
						index_of_target(&distribution[5usize].0).or_invalid_index()?,
					)),
					7usize => compact.votes7.push((
						index_of_voter(&who).or_invalid_index()?,
						[
							(
								index_of_target(&distribution[0usize].0).or_invalid_index()?,
								distribution[0usize].1,
							),
							(
								index_of_target(&distribution[1usize].0).or_invalid_index()?,
								distribution[1usize].1,
							),
							(
								index_of_target(&distribution[2usize].0).or_invalid_index()?,
								distribution[2usize].1,
							),
							(
								index_of_target(&distribution[3usize].0).or_invalid_index()?,
								distribution[3usize].1,
							),
							(
								index_of_target(&distribution[4usize].0).or_invalid_index()?,
								distribution[4usize].1,
							),
							(
								index_of_target(&distribution[5usize].0).or_invalid_index()?,
								distribution[5usize].1,
							),
						],
						index_of_target(&distribution[6usize].0).or_invalid_index()?,
					)),
					8usize => compact.votes8.push((
						index_of_voter(&who).or_invalid_index()?,
						[
							(
								index_of_target(&distribution[0usize].0).or_invalid_index()?,
								distribution[0usize].1,
							),
							(
								index_of_target(&distribution[1usize].0).or_invalid_index()?,
								distribution[1usize].1,
							),
							(
								index_of_target(&distribution[2usize].0).or_invalid_index()?,
								distribution[2usize].1,
							),
							(
								index_of_target(&distribution[3usize].0).or_invalid_index()?,
								distribution[3usize].1,
							),
							(
								index_of_target(&distribution[4usize].0).or_invalid_index()?,
								distribution[4usize].1,
							),
							(
								index_of_target(&distribution[5usize].0).or_invalid_index()?,
								distribution[5usize].1,
							),
							(
								index_of_target(&distribution[6usize].0).or_invalid_index()?,
								distribution[6usize].1,
							),
						],
						index_of_target(&distribution[7usize].0).or_invalid_index()?,
					)),
					9usize => compact.votes9.push((
						index_of_voter(&who).or_invalid_index()?,
						[
							(
								index_of_target(&distribution[0usize].0).or_invalid_index()?,
								distribution[0usize].1,
							),
							(
								index_of_target(&distribution[1usize].0).or_invalid_index()?,
								distribution[1usize].1,
							),
							(
								index_of_target(&distribution[2usize].0).or_invalid_index()?,
								distribution[2usize].1,
							),
							(
								index_of_target(&distribution[3usize].0).or_invalid_index()?,
								distribution[3usize].1,
							),
							(
								index_of_target(&distribution[4usize].0).or_invalid_index()?,
								distribution[4usize].1,
							),
							(
								index_of_target(&distribution[5usize].0).or_invalid_index()?,
								distribution[5usize].1,
							),
							(
								index_of_target(&distribution[6usize].0).or_invalid_index()?,
								distribution[6usize].1,
							),
							(
								index_of_target(&distribution[7usize].0).or_invalid_index()?,
								distribution[7usize].1,
							),
						],
						index_of_target(&distribution[8usize].0).or_invalid_index()?,
					)),
					10usize => compact.votes10.push((
						index_of_voter(&who).or_invalid_index()?,
						[
							(
								index_of_target(&distribution[0usize].0).or_invalid_index()?,
								distribution[0usize].1,
							),
							(
								index_of_target(&distribution[1usize].0).or_invalid_index()?,
								distribution[1usize].1,
							),
							(
								index_of_target(&distribution[2usize].0).or_invalid_index()?,
								distribution[2usize].1,
							),
							(
								index_of_target(&distribution[3usize].0).or_invalid_index()?,
								distribution[3usize].1,
							),
							(
								index_of_target(&distribution[4usize].0).or_invalid_index()?,
								distribution[4usize].1,
							),
							(
								index_of_target(&distribution[5usize].0).or_invalid_index()?,
								distribution[5usize].1,
							),
							(
								index_of_target(&distribution[6usize].0).or_invalid_index()?,
								distribution[6usize].1,
							),
							(
								index_of_target(&distribution[7usize].0).or_invalid_index()?,
								distribution[7usize].1,
							),
							(
								index_of_target(&distribution[8usize].0).or_invalid_index()?,
								distribution[8usize].1,
							),
						],
						index_of_target(&distribution[9usize].0).or_invalid_index()?,
					)),
					11usize => compact.votes11.push((
						index_of_voter(&who).or_invalid_index()?,
						[
							(
								index_of_target(&distribution[0usize].0).or_invalid_index()?,
								distribution[0usize].1,
							),
							(
								index_of_target(&distribution[1usize].0).or_invalid_index()?,
								distribution[1usize].1,
							),
							(
								index_of_target(&distribution[2usize].0).or_invalid_index()?,
								distribution[2usize].1,
							),
							(
								index_of_target(&distribution[3usize].0).or_invalid_index()?,
								distribution[3usize].1,
							),
							(
								index_of_target(&distribution[4usize].0).or_invalid_index()?,
								distribution[4usize].1,
							),
							(
								index_of_target(&distribution[5usize].0).or_invalid_index()?,
								distribution[5usize].1,
							),
							(
								index_of_target(&distribution[6usize].0).or_invalid_index()?,
								distribution[6usize].1,
							),
							(
								index_of_target(&distribution[7usize].0).or_invalid_index()?,
								distribution[7usize].1,
							),
							(
								index_of_target(&distribution[8usize].0).or_invalid_index()?,
								distribution[8usize].1,
							),
							(
								index_of_target(&distribution[9usize].0).or_invalid_index()?,
								distribution[9usize].1,
							),
						],
						index_of_target(&distribution[10usize].0).or_invalid_index()?,
					)),
					12usize => compact.votes12.push((
						index_of_voter(&who).or_invalid_index()?,
						[
							(
								index_of_target(&distribution[0usize].0).or_invalid_index()?,
								distribution[0usize].1,
							),
							(
								index_of_target(&distribution[1usize].0).or_invalid_index()?,
								distribution[1usize].1,
							),
							(
								index_of_target(&distribution[2usize].0).or_invalid_index()?,
								distribution[2usize].1,
							),
							(
								index_of_target(&distribution[3usize].0).or_invalid_index()?,
								distribution[3usize].1,
							),
							(
								index_of_target(&distribution[4usize].0).or_invalid_index()?,
								distribution[4usize].1,
							),
							(
								index_of_target(&distribution[5usize].0).or_invalid_index()?,
								distribution[5usize].1,
							),
							(
								index_of_target(&distribution[6usize].0).or_invalid_index()?,
								distribution[6usize].1,
							),
							(
								index_of_target(&distribution[7usize].0).or_invalid_index()?,
								distribution[7usize].1,
							),
							(
								index_of_target(&distribution[8usize].0).or_invalid_index()?,
								distribution[8usize].1,
							),
							(
								index_of_target(&distribution[9usize].0).or_invalid_index()?,
								distribution[9usize].1,
							),
							(
								index_of_target(&distribution[10usize].0).or_invalid_index()?,
								distribution[10usize].1,
							),
						],
						index_of_target(&distribution[11usize].0).or_invalid_index()?,
					)),
					13usize => compact.votes13.push((
						index_of_voter(&who).or_invalid_index()?,
						[
							(
								index_of_target(&distribution[0usize].0).or_invalid_index()?,
								distribution[0usize].1,
							),
							(
								index_of_target(&distribution[1usize].0).or_invalid_index()?,
								distribution[1usize].1,
							),
							(
								index_of_target(&distribution[2usize].0).or_invalid_index()?,
								distribution[2usize].1,
							),
							(
								index_of_target(&distribution[3usize].0).or_invalid_index()?,
								distribution[3usize].1,
							),
							(
								index_of_target(&distribution[4usize].0).or_invalid_index()?,
								distribution[4usize].1,
							),
							(
								index_of_target(&distribution[5usize].0).or_invalid_index()?,
								distribution[5usize].1,
							),
							(
								index_of_target(&distribution[6usize].0).or_invalid_index()?,
								distribution[6usize].1,
							),
							(
								index_of_target(&distribution[7usize].0).or_invalid_index()?,
								distribution[7usize].1,
							),
							(
								index_of_target(&distribution[8usize].0).or_invalid_index()?,
								distribution[8usize].1,
							),
							(
								index_of_target(&distribution[9usize].0).or_invalid_index()?,
								distribution[9usize].1,
							),
							(
								index_of_target(&distribution[10usize].0).or_invalid_index()?,
								distribution[10usize].1,
							),
							(
								index_of_target(&distribution[11usize].0).or_invalid_index()?,
								distribution[11usize].1,
							),
						],
						index_of_target(&distribution[12usize].0).or_invalid_index()?,
					)),
					14usize => compact.votes14.push((
						index_of_voter(&who).or_invalid_index()?,
						[
							(
								index_of_target(&distribution[0usize].0).or_invalid_index()?,
								distribution[0usize].1,
							),
							(
								index_of_target(&distribution[1usize].0).or_invalid_index()?,
								distribution[1usize].1,
							),
							(
								index_of_target(&distribution[2usize].0).or_invalid_index()?,
								distribution[2usize].1,
							),
							(
								index_of_target(&distribution[3usize].0).or_invalid_index()?,
								distribution[3usize].1,
							),
							(
								index_of_target(&distribution[4usize].0).or_invalid_index()?,
								distribution[4usize].1,
							),
							(
								index_of_target(&distribution[5usize].0).or_invalid_index()?,
								distribution[5usize].1,
							),
							(
								index_of_target(&distribution[6usize].0).or_invalid_index()?,
								distribution[6usize].1,
							),
							(
								index_of_target(&distribution[7usize].0).or_invalid_index()?,
								distribution[7usize].1,
							),
							(
								index_of_target(&distribution[8usize].0).or_invalid_index()?,
								distribution[8usize].1,
							),
							(
								index_of_target(&distribution[9usize].0).or_invalid_index()?,
								distribution[9usize].1,
							),
							(
								index_of_target(&distribution[10usize].0).or_invalid_index()?,
								distribution[10usize].1,
							),
							(
								index_of_target(&distribution[11usize].0).or_invalid_index()?,
								distribution[11usize].1,
							),
							(
								index_of_target(&distribution[12usize].0).or_invalid_index()?,
								distribution[12usize].1,
							),
						],
						index_of_target(&distribution[13usize].0).or_invalid_index()?,
					)),
					15usize => compact.votes15.push((
						index_of_voter(&who).or_invalid_index()?,
						[
							(
								index_of_target(&distribution[0usize].0).or_invalid_index()?,
								distribution[0usize].1,
							),
							(
								index_of_target(&distribution[1usize].0).or_invalid_index()?,
								distribution[1usize].1,
							),
							(
								index_of_target(&distribution[2usize].0).or_invalid_index()?,
								distribution[2usize].1,
							),
							(
								index_of_target(&distribution[3usize].0).or_invalid_index()?,
								distribution[3usize].1,
							),
							(
								index_of_target(&distribution[4usize].0).or_invalid_index()?,
								distribution[4usize].1,
							),
							(
								index_of_target(&distribution[5usize].0).or_invalid_index()?,
								distribution[5usize].1,
							),
							(
								index_of_target(&distribution[6usize].0).or_invalid_index()?,
								distribution[6usize].1,
							),
							(
								index_of_target(&distribution[7usize].0).or_invalid_index()?,
								distribution[7usize].1,
							),
							(
								index_of_target(&distribution[8usize].0).or_invalid_index()?,
								distribution[8usize].1,
							),
							(
								index_of_target(&distribution[9usize].0).or_invalid_index()?,
								distribution[9usize].1,
							),
							(
								index_of_target(&distribution[10usize].0).or_invalid_index()?,
								distribution[10usize].1,
							),
							(
								index_of_target(&distribution[11usize].0).or_invalid_index()?,
								distribution[11usize].1,
							),
							(
								index_of_target(&distribution[12usize].0).or_invalid_index()?,
								distribution[12usize].1,
							),
							(
								index_of_target(&distribution[13usize].0).or_invalid_index()?,
								distribution[13usize].1,
							),
						],
						index_of_target(&distribution[14usize].0).or_invalid_index()?,
					)),
					16usize => compact.votes16.push((
						index_of_voter(&who).or_invalid_index()?,
						[
							(
								index_of_target(&distribution[0usize].0).or_invalid_index()?,
								distribution[0usize].1,
							),
							(
								index_of_target(&distribution[1usize].0).or_invalid_index()?,
								distribution[1usize].1,
							),
							(
								index_of_target(&distribution[2usize].0).or_invalid_index()?,
								distribution[2usize].1,
							),
							(
								index_of_target(&distribution[3usize].0).or_invalid_index()?,
								distribution[3usize].1,
							),
							(
								index_of_target(&distribution[4usize].0).or_invalid_index()?,
								distribution[4usize].1,
							),
							(
								index_of_target(&distribution[5usize].0).or_invalid_index()?,
								distribution[5usize].1,
							),
							(
								index_of_target(&distribution[6usize].0).or_invalid_index()?,
								distribution[6usize].1,
							),
							(
								index_of_target(&distribution[7usize].0).or_invalid_index()?,
								distribution[7usize].1,
							),
							(
								index_of_target(&distribution[8usize].0).or_invalid_index()?,
								distribution[8usize].1,
							),
							(
								index_of_target(&distribution[9usize].0).or_invalid_index()?,
								distribution[9usize].1,
							),
							(
								index_of_target(&distribution[10usize].0).or_invalid_index()?,
								distribution[10usize].1,
							),
							(
								index_of_target(&distribution[11usize].0).or_invalid_index()?,
								distribution[11usize].1,
							),
							(
								index_of_target(&distribution[12usize].0).or_invalid_index()?,
								distribution[12usize].1,
							),
							(
								index_of_target(&distribution[13usize].0).or_invalid_index()?,
								distribution[13usize].1,
							),
							(
								index_of_target(&distribution[14usize].0).or_invalid_index()?,
								distribution[14usize].1,
							),
						],
						index_of_target(&distribution[15usize].0).or_invalid_index()?,
					)),
					_ => {
						return Err(_npos::Error::CompactTargetOverflow);
					}
				}
			}
			Ok(compact)
		}
		pub fn into_assignment<A: _npos::IdentifierT>(
			self,
			voter_at: impl Fn(VoterIndex) -> Option<A>,
			target_at: impl Fn(TargetIndex) -> Option<A>,
		) -> Result<Vec<_npos::Assignment<A, OffchainAccuracy>>, _npos::Error> {
			let mut assignments: Vec<_npos::Assignment<A, OffchainAccuracy>> = Default::default();
			for (voter_index, target_index) in self.votes1 {
				assignments.push(_npos::Assignment {
					who: voter_at(voter_index).or_invalid_index()?,
					distribution: <[_]>::into_vec(box [(
						target_at(target_index).or_invalid_index()?,
						OffchainAccuracy::one(),
					)]),
				})
			}
			for (voter_index, (t1_idx, p1), t2_idx) in self.votes2 {
				if p1 >= OffchainAccuracy::one() {
					return Err(_npos::Error::CompactStakeOverflow);
				}
				let p2 = _npos::sp_arithmetic::traits::Saturating::saturating_sub(
					OffchainAccuracy::one(),
					p1,
				);
				assignments.push(_npos::Assignment {
					who: voter_at(voter_index).or_invalid_index()?,
					distribution: <[_]>::into_vec(box [
						(target_at(t1_idx).or_invalid_index()?, p1),
						(target_at(t2_idx).or_invalid_index()?, p2),
					]),
				});
			}
			for (voter_index, inners, t_last_idx) in self.votes3 {
				let mut sum = OffchainAccuracy::zero();
				let mut inners_parsed = inners
					.iter()
					.map(|(ref t_idx, p)| {
						sum = _npos::sp_arithmetic::traits::Saturating::saturating_add(sum, *p);
						let target = target_at(*t_idx).or_invalid_index()?;
						Ok((target, *p))
					})
					.collect::<Result<Vec<(A, OffchainAccuracy)>, _npos::Error>>()?;
				if sum >= OffchainAccuracy::one() {
					return Err(_npos::Error::CompactStakeOverflow);
				}
				let p_last = _npos::sp_arithmetic::traits::Saturating::saturating_sub(
					OffchainAccuracy::one(),
					sum,
				);
				inners_parsed.push((target_at(t_last_idx).or_invalid_index()?, p_last));
				assignments.push(_npos::Assignment {
					who: voter_at(voter_index).or_invalid_index()?,
					distribution: inners_parsed,
				});
			}
			for (voter_index, inners, t_last_idx) in self.votes4 {
				let mut sum = OffchainAccuracy::zero();
				let mut inners_parsed = inners
					.iter()
					.map(|(ref t_idx, p)| {
						sum = _npos::sp_arithmetic::traits::Saturating::saturating_add(sum, *p);
						let target = target_at(*t_idx).or_invalid_index()?;
						Ok((target, *p))
					})
					.collect::<Result<Vec<(A, OffchainAccuracy)>, _npos::Error>>()?;
				if sum >= OffchainAccuracy::one() {
					return Err(_npos::Error::CompactStakeOverflow);
				}
				let p_last = _npos::sp_arithmetic::traits::Saturating::saturating_sub(
					OffchainAccuracy::one(),
					sum,
				);
				inners_parsed.push((target_at(t_last_idx).or_invalid_index()?, p_last));
				assignments.push(_npos::Assignment {
					who: voter_at(voter_index).or_invalid_index()?,
					distribution: inners_parsed,
				});
			}
			for (voter_index, inners, t_last_idx) in self.votes5 {
				let mut sum = OffchainAccuracy::zero();
				let mut inners_parsed = inners
					.iter()
					.map(|(ref t_idx, p)| {
						sum = _npos::sp_arithmetic::traits::Saturating::saturating_add(sum, *p);
						let target = target_at(*t_idx).or_invalid_index()?;
						Ok((target, *p))
					})
					.collect::<Result<Vec<(A, OffchainAccuracy)>, _npos::Error>>()?;
				if sum >= OffchainAccuracy::one() {
					return Err(_npos::Error::CompactStakeOverflow);
				}
				let p_last = _npos::sp_arithmetic::traits::Saturating::saturating_sub(
					OffchainAccuracy::one(),
					sum,
				);
				inners_parsed.push((target_at(t_last_idx).or_invalid_index()?, p_last));
				assignments.push(_npos::Assignment {
					who: voter_at(voter_index).or_invalid_index()?,
					distribution: inners_parsed,
				});
			}
			for (voter_index, inners, t_last_idx) in self.votes6 {
				let mut sum = OffchainAccuracy::zero();
				let mut inners_parsed = inners
					.iter()
					.map(|(ref t_idx, p)| {
						sum = _npos::sp_arithmetic::traits::Saturating::saturating_add(sum, *p);
						let target = target_at(*t_idx).or_invalid_index()?;
						Ok((target, *p))
					})
					.collect::<Result<Vec<(A, OffchainAccuracy)>, _npos::Error>>()?;
				if sum >= OffchainAccuracy::one() {
					return Err(_npos::Error::CompactStakeOverflow);
				}
				let p_last = _npos::sp_arithmetic::traits::Saturating::saturating_sub(
					OffchainAccuracy::one(),
					sum,
				);
				inners_parsed.push((target_at(t_last_idx).or_invalid_index()?, p_last));
				assignments.push(_npos::Assignment {
					who: voter_at(voter_index).or_invalid_index()?,
					distribution: inners_parsed,
				});
			}
			for (voter_index, inners, t_last_idx) in self.votes7 {
				let mut sum = OffchainAccuracy::zero();
				let mut inners_parsed = inners
					.iter()
					.map(|(ref t_idx, p)| {
						sum = _npos::sp_arithmetic::traits::Saturating::saturating_add(sum, *p);
						let target = target_at(*t_idx).or_invalid_index()?;
						Ok((target, *p))
					})
					.collect::<Result<Vec<(A, OffchainAccuracy)>, _npos::Error>>()?;
				if sum >= OffchainAccuracy::one() {
					return Err(_npos::Error::CompactStakeOverflow);
				}
				let p_last = _npos::sp_arithmetic::traits::Saturating::saturating_sub(
					OffchainAccuracy::one(),
					sum,
				);
				inners_parsed.push((target_at(t_last_idx).or_invalid_index()?, p_last));
				assignments.push(_npos::Assignment {
					who: voter_at(voter_index).or_invalid_index()?,
					distribution: inners_parsed,
				});
			}
			for (voter_index, inners, t_last_idx) in self.votes8 {
				let mut sum = OffchainAccuracy::zero();
				let mut inners_parsed = inners
					.iter()
					.map(|(ref t_idx, p)| {
						sum = _npos::sp_arithmetic::traits::Saturating::saturating_add(sum, *p);
						let target = target_at(*t_idx).or_invalid_index()?;
						Ok((target, *p))
					})
					.collect::<Result<Vec<(A, OffchainAccuracy)>, _npos::Error>>()?;
				if sum >= OffchainAccuracy::one() {
					return Err(_npos::Error::CompactStakeOverflow);
				}
				let p_last = _npos::sp_arithmetic::traits::Saturating::saturating_sub(
					OffchainAccuracy::one(),
					sum,
				);
				inners_parsed.push((target_at(t_last_idx).or_invalid_index()?, p_last));
				assignments.push(_npos::Assignment {
					who: voter_at(voter_index).or_invalid_index()?,
					distribution: inners_parsed,
				});
			}
			for (voter_index, inners, t_last_idx) in self.votes9 {
				let mut sum = OffchainAccuracy::zero();
				let mut inners_parsed = inners
					.iter()
					.map(|(ref t_idx, p)| {
						sum = _npos::sp_arithmetic::traits::Saturating::saturating_add(sum, *p);
						let target = target_at(*t_idx).or_invalid_index()?;
						Ok((target, *p))
					})
					.collect::<Result<Vec<(A, OffchainAccuracy)>, _npos::Error>>()?;
				if sum >= OffchainAccuracy::one() {
					return Err(_npos::Error::CompactStakeOverflow);
				}
				let p_last = _npos::sp_arithmetic::traits::Saturating::saturating_sub(
					OffchainAccuracy::one(),
					sum,
				);
				inners_parsed.push((target_at(t_last_idx).or_invalid_index()?, p_last));
				assignments.push(_npos::Assignment {
					who: voter_at(voter_index).or_invalid_index()?,
					distribution: inners_parsed,
				});
			}
			for (voter_index, inners, t_last_idx) in self.votes10 {
				let mut sum = OffchainAccuracy::zero();
				let mut inners_parsed = inners
					.iter()
					.map(|(ref t_idx, p)| {
						sum = _npos::sp_arithmetic::traits::Saturating::saturating_add(sum, *p);
						let target = target_at(*t_idx).or_invalid_index()?;
						Ok((target, *p))
					})
					.collect::<Result<Vec<(A, OffchainAccuracy)>, _npos::Error>>()?;
				if sum >= OffchainAccuracy::one() {
					return Err(_npos::Error::CompactStakeOverflow);
				}
				let p_last = _npos::sp_arithmetic::traits::Saturating::saturating_sub(
					OffchainAccuracy::one(),
					sum,
				);
				inners_parsed.push((target_at(t_last_idx).or_invalid_index()?, p_last));
				assignments.push(_npos::Assignment {
					who: voter_at(voter_index).or_invalid_index()?,
					distribution: inners_parsed,
				});
			}
			for (voter_index, inners, t_last_idx) in self.votes11 {
				let mut sum = OffchainAccuracy::zero();
				let mut inners_parsed = inners
					.iter()
					.map(|(ref t_idx, p)| {
						sum = _npos::sp_arithmetic::traits::Saturating::saturating_add(sum, *p);
						let target = target_at(*t_idx).or_invalid_index()?;
						Ok((target, *p))
					})
					.collect::<Result<Vec<(A, OffchainAccuracy)>, _npos::Error>>()?;
				if sum >= OffchainAccuracy::one() {
					return Err(_npos::Error::CompactStakeOverflow);
				}
				let p_last = _npos::sp_arithmetic::traits::Saturating::saturating_sub(
					OffchainAccuracy::one(),
					sum,
				);
				inners_parsed.push((target_at(t_last_idx).or_invalid_index()?, p_last));
				assignments.push(_npos::Assignment {
					who: voter_at(voter_index).or_invalid_index()?,
					distribution: inners_parsed,
				});
			}
			for (voter_index, inners, t_last_idx) in self.votes12 {
				let mut sum = OffchainAccuracy::zero();
				let mut inners_parsed = inners
					.iter()
					.map(|(ref t_idx, p)| {
						sum = _npos::sp_arithmetic::traits::Saturating::saturating_add(sum, *p);
						let target = target_at(*t_idx).or_invalid_index()?;
						Ok((target, *p))
					})
					.collect::<Result<Vec<(A, OffchainAccuracy)>, _npos::Error>>()?;
				if sum >= OffchainAccuracy::one() {
					return Err(_npos::Error::CompactStakeOverflow);
				}
				let p_last = _npos::sp_arithmetic::traits::Saturating::saturating_sub(
					OffchainAccuracy::one(),
					sum,
				);
				inners_parsed.push((target_at(t_last_idx).or_invalid_index()?, p_last));
				assignments.push(_npos::Assignment {
					who: voter_at(voter_index).or_invalid_index()?,
					distribution: inners_parsed,
				});
			}
			for (voter_index, inners, t_last_idx) in self.votes13 {
				let mut sum = OffchainAccuracy::zero();
				let mut inners_parsed = inners
					.iter()
					.map(|(ref t_idx, p)| {
						sum = _npos::sp_arithmetic::traits::Saturating::saturating_add(sum, *p);
						let target = target_at(*t_idx).or_invalid_index()?;
						Ok((target, *p))
					})
					.collect::<Result<Vec<(A, OffchainAccuracy)>, _npos::Error>>()?;
				if sum >= OffchainAccuracy::one() {
					return Err(_npos::Error::CompactStakeOverflow);
				}
				let p_last = _npos::sp_arithmetic::traits::Saturating::saturating_sub(
					OffchainAccuracy::one(),
					sum,
				);
				inners_parsed.push((target_at(t_last_idx).or_invalid_index()?, p_last));
				assignments.push(_npos::Assignment {
					who: voter_at(voter_index).or_invalid_index()?,
					distribution: inners_parsed,
				});
			}
			for (voter_index, inners, t_last_idx) in self.votes14 {
				let mut sum = OffchainAccuracy::zero();
				let mut inners_parsed = inners
					.iter()
					.map(|(ref t_idx, p)| {
						sum = _npos::sp_arithmetic::traits::Saturating::saturating_add(sum, *p);
						let target = target_at(*t_idx).or_invalid_index()?;
						Ok((target, *p))
					})
					.collect::<Result<Vec<(A, OffchainAccuracy)>, _npos::Error>>()?;
				if sum >= OffchainAccuracy::one() {
					return Err(_npos::Error::CompactStakeOverflow);
				}
				let p_last = _npos::sp_arithmetic::traits::Saturating::saturating_sub(
					OffchainAccuracy::one(),
					sum,
				);
				inners_parsed.push((target_at(t_last_idx).or_invalid_index()?, p_last));
				assignments.push(_npos::Assignment {
					who: voter_at(voter_index).or_invalid_index()?,
					distribution: inners_parsed,
				});
			}
			for (voter_index, inners, t_last_idx) in self.votes15 {
				let mut sum = OffchainAccuracy::zero();
				let mut inners_parsed = inners
					.iter()
					.map(|(ref t_idx, p)| {
						sum = _npos::sp_arithmetic::traits::Saturating::saturating_add(sum, *p);
						let target = target_at(*t_idx).or_invalid_index()?;
						Ok((target, *p))
					})
					.collect::<Result<Vec<(A, OffchainAccuracy)>, _npos::Error>>()?;
				if sum >= OffchainAccuracy::one() {
					return Err(_npos::Error::CompactStakeOverflow);
				}
				let p_last = _npos::sp_arithmetic::traits::Saturating::saturating_sub(
					OffchainAccuracy::one(),
					sum,
				);
				inners_parsed.push((target_at(t_last_idx).or_invalid_index()?, p_last));
				assignments.push(_npos::Assignment {
					who: voter_at(voter_index).or_invalid_index()?,
					distribution: inners_parsed,
				});
			}
			for (voter_index, inners, t_last_idx) in self.votes16 {
				let mut sum = OffchainAccuracy::zero();
				let mut inners_parsed = inners
					.iter()
					.map(|(ref t_idx, p)| {
						sum = _npos::sp_arithmetic::traits::Saturating::saturating_add(sum, *p);
						let target = target_at(*t_idx).or_invalid_index()?;
						Ok((target, *p))
					})
					.collect::<Result<Vec<(A, OffchainAccuracy)>, _npos::Error>>()?;
				if sum >= OffchainAccuracy::one() {
					return Err(_npos::Error::CompactStakeOverflow);
				}
				let p_last = _npos::sp_arithmetic::traits::Saturating::saturating_sub(
					OffchainAccuracy::one(),
					sum,
				);
				inners_parsed.push((target_at(t_last_idx).or_invalid_index()?, p_last));
				assignments.push(_npos::Assignment {
					who: voter_at(voter_index).or_invalid_index()?,
					distribution: inners_parsed,
				});
			}
			Ok(assignments)
		}
	}
	const LOG_TARGET: &'static str = "two-phase-submission";
	pub enum Phase {
		Off,
		Signed,
		Unsigned(bool),
	}
	impl ::core::marker::StructuralPartialEq for Phase {}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl ::core::cmp::PartialEq for Phase {
		#[inline]
		fn eq(&self, other: &Phase) -> bool {
			{
				let __self_vi = unsafe { ::core::intrinsics::discriminant_value(&*self) };
				let __arg_1_vi = unsafe { ::core::intrinsics::discriminant_value(&*other) };
				if true && __self_vi == __arg_1_vi {
					match (&*self, &*other) {
						(&Phase::Unsigned(ref __self_0), &Phase::Unsigned(ref __arg_1_0)) => {
							(*__self_0) == (*__arg_1_0)
						}
						_ => true,
					}
				} else {
					false
				}
			}
		}
		#[inline]
		fn ne(&self, other: &Phase) -> bool {
			{
				let __self_vi = unsafe { ::core::intrinsics::discriminant_value(&*self) };
				let __arg_1_vi = unsafe { ::core::intrinsics::discriminant_value(&*other) };
				if true && __self_vi == __arg_1_vi {
					match (&*self, &*other) {
						(&Phase::Unsigned(ref __self_0), &Phase::Unsigned(ref __arg_1_0)) => {
							(*__self_0) != (*__arg_1_0)
						}
						_ => false,
					}
				} else {
					true
				}
			}
		}
	}
	impl ::core::marker::StructuralEq for Phase {}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl ::core::cmp::Eq for Phase {
		#[inline]
		#[doc(hidden)]
		fn assert_receiver_is_total_eq(&self) -> () {
			{
				let _: ::core::cmp::AssertParamIsEq<bool>;
			}
		}
	}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl ::core::clone::Clone for Phase {
		#[inline]
		fn clone(&self) -> Phase {
			{
				let _: ::core::clone::AssertParamIsClone<bool>;
				*self
			}
		}
	}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl ::core::marker::Copy for Phase {}
	const _: () = {
		#[allow(unknown_lints)]
		#[allow(rust_2018_idioms)]
		extern crate codec as _parity_scale_codec;
		impl _parity_scale_codec::Encode for Phase {
			fn encode_to<EncOut: _parity_scale_codec::Output>(&self, dest: &mut EncOut) {
				match *self {
					Phase::Off => {
						dest.push_byte(0usize as u8);
					}
					Phase::Signed => {
						dest.push_byte(1usize as u8);
					}
					Phase::Unsigned(ref aa) => {
						dest.push_byte(2usize as u8);
						dest.push(aa);
					}
					_ => (),
				}
			}
		}
		impl _parity_scale_codec::EncodeLike for Phase {}
	};
	const _: () = {
		#[allow(unknown_lints)]
		#[allow(rust_2018_idioms)]
		extern crate codec as _parity_scale_codec;
		impl _parity_scale_codec::Decode for Phase {
			fn decode<DecIn: _parity_scale_codec::Input>(
				input: &mut DecIn,
			) -> core::result::Result<Self, _parity_scale_codec::Error> {
				match input.read_byte()? {
					x if x == 0usize as u8 => Ok(Phase::Off),
					x if x == 1usize as u8 => Ok(Phase::Signed),
					x if x == 2usize as u8 => Ok(Phase::Unsigned({
						let res = _parity_scale_codec::Decode::decode(input);
						match res {
							Err(_) => return Err("Error decoding field Phase :: Unsigned.0".into()),
							Ok(a) => a,
						}
					})),
					x => Err("No such variant in enum Phase".into()),
				}
			}
		}
	};
	impl core::fmt::Debug for Phase {
		fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
			match self {
				Self::Off => fmt.debug_tuple("Phase::Off").finish(),
				Self::Signed => fmt.debug_tuple("Phase::Signed").finish(),
				Self::Unsigned(ref a0) => fmt.debug_tuple("Phase::Unsigned").field(a0).finish(),
				_ => Ok(()),
			}
		}
	}
	impl Default for Phase {
		fn default() -> Self {
			Phase::Off
		}
	}
	impl Phase {
		pub fn is_signed(&self) -> bool {
			match self {
				Phase::Signed => true,
				_ => false,
			}
		}
		pub fn is_unsigned(&self) -> bool {
			match self {
				Phase::Unsigned(_) => true,
				_ => false,
			}
		}
		pub fn is_unsigned_open(&self) -> bool {
			match self {
				Phase::Unsigned(true) => true,
				_ => false,
			}
		}
		pub fn is_off(&self) -> bool {
			match self {
				Phase::Off => true,
				_ => false,
			}
		}
	}
	pub enum ElectionCompute {
		OnChain,
		Signed,
		Unsigned,
	}
	impl ::core::marker::StructuralPartialEq for ElectionCompute {}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl ::core::cmp::PartialEq for ElectionCompute {
		#[inline]
		fn eq(&self, other: &ElectionCompute) -> bool {
			{
				let __self_vi = unsafe { ::core::intrinsics::discriminant_value(&*self) };
				let __arg_1_vi = unsafe { ::core::intrinsics::discriminant_value(&*other) };
				if true && __self_vi == __arg_1_vi {
					match (&*self, &*other) {
						_ => true,
					}
				} else {
					false
				}
			}
		}
	}
	impl ::core::marker::StructuralEq for ElectionCompute {}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl ::core::cmp::Eq for ElectionCompute {
		#[inline]
		#[doc(hidden)]
		fn assert_receiver_is_total_eq(&self) -> () {
			{}
		}
	}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl ::core::clone::Clone for ElectionCompute {
		#[inline]
		fn clone(&self) -> ElectionCompute {
			{
				*self
			}
		}
	}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl ::core::marker::Copy for ElectionCompute {}
	const _: () = {
		#[allow(unknown_lints)]
		#[allow(rust_2018_idioms)]
		extern crate codec as _parity_scale_codec;
		impl _parity_scale_codec::Encode for ElectionCompute {
			fn encode_to<EncOut: _parity_scale_codec::Output>(&self, dest: &mut EncOut) {
				match *self {
					ElectionCompute::OnChain => {
						dest.push_byte(0usize as u8);
					}
					ElectionCompute::Signed => {
						dest.push_byte(1usize as u8);
					}
					ElectionCompute::Unsigned => {
						dest.push_byte(2usize as u8);
					}
					_ => (),
				}
			}
		}
		impl _parity_scale_codec::EncodeLike for ElectionCompute {}
	};
	const _: () = {
		#[allow(unknown_lints)]
		#[allow(rust_2018_idioms)]
		extern crate codec as _parity_scale_codec;
		impl _parity_scale_codec::Decode for ElectionCompute {
			fn decode<DecIn: _parity_scale_codec::Input>(
				input: &mut DecIn,
			) -> core::result::Result<Self, _parity_scale_codec::Error> {
				match input.read_byte()? {
					x if x == 0usize as u8 => Ok(ElectionCompute::OnChain),
					x if x == 1usize as u8 => Ok(ElectionCompute::Signed),
					x if x == 2usize as u8 => Ok(ElectionCompute::Unsigned),
					x => Err("No such variant in enum ElectionCompute".into()),
				}
			}
		}
	};
	impl core::fmt::Debug for ElectionCompute {
		fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
			match self {
				Self::OnChain => fmt.debug_tuple("ElectionCompute::OnChain").finish(),
				Self::Signed => fmt.debug_tuple("ElectionCompute::Signed").finish(),
				Self::Unsigned => fmt.debug_tuple("ElectionCompute::Unsigned").finish(),
				_ => Ok(()),
			}
		}
	}
	impl Default for ElectionCompute {
		fn default() -> Self {
			ElectionCompute::OnChain
		}
	}
	pub struct RawSolution {
		winners: Vec<TargetIndex>,
		compact: CompactAssignments,
		score: ElectionScore,
	}
	impl ::core::marker::StructuralPartialEq for RawSolution {}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl ::core::cmp::PartialEq for RawSolution {
		#[inline]
		fn eq(&self, other: &RawSolution) -> bool {
			match *other {
				RawSolution {
					winners: ref __self_1_0,
					compact: ref __self_1_1,
					score: ref __self_1_2,
				} => match *self {
					RawSolution {
						winners: ref __self_0_0,
						compact: ref __self_0_1,
						score: ref __self_0_2,
					} => {
						(*__self_0_0) == (*__self_1_0)
							&& (*__self_0_1) == (*__self_1_1)
							&& (*__self_0_2) == (*__self_1_2)
					}
				},
			}
		}
		#[inline]
		fn ne(&self, other: &RawSolution) -> bool {
			match *other {
				RawSolution {
					winners: ref __self_1_0,
					compact: ref __self_1_1,
					score: ref __self_1_2,
				} => match *self {
					RawSolution {
						winners: ref __self_0_0,
						compact: ref __self_0_1,
						score: ref __self_0_2,
					} => {
						(*__self_0_0) != (*__self_1_0)
							|| (*__self_0_1) != (*__self_1_1)
							|| (*__self_0_2) != (*__self_1_2)
					}
				},
			}
		}
	}
	impl ::core::marker::StructuralEq for RawSolution {}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl ::core::cmp::Eq for RawSolution {
		#[inline]
		#[doc(hidden)]
		fn assert_receiver_is_total_eq(&self) -> () {
			{
				let _: ::core::cmp::AssertParamIsEq<Vec<TargetIndex>>;
				let _: ::core::cmp::AssertParamIsEq<CompactAssignments>;
				let _: ::core::cmp::AssertParamIsEq<ElectionScore>;
			}
		}
	}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl ::core::clone::Clone for RawSolution {
		#[inline]
		fn clone(&self) -> RawSolution {
			match *self {
				RawSolution {
					winners: ref __self_0_0,
					compact: ref __self_0_1,
					score: ref __self_0_2,
				} => RawSolution {
					winners: ::core::clone::Clone::clone(&(*__self_0_0)),
					compact: ::core::clone::Clone::clone(&(*__self_0_1)),
					score: ::core::clone::Clone::clone(&(*__self_0_2)),
				},
			}
		}
	}
	const _: () = {
		#[allow(unknown_lints)]
		#[allow(rust_2018_idioms)]
		extern crate codec as _parity_scale_codec;
		impl _parity_scale_codec::Encode for RawSolution {
			fn encode_to<EncOut: _parity_scale_codec::Output>(&self, dest: &mut EncOut) {
				dest.push(&self.winners);
				dest.push(&self.compact);
				dest.push(&self.score);
			}
		}
		impl _parity_scale_codec::EncodeLike for RawSolution {}
	};
	const _: () = {
		#[allow(unknown_lints)]
		#[allow(rust_2018_idioms)]
		extern crate codec as _parity_scale_codec;
		impl _parity_scale_codec::Decode for RawSolution {
			fn decode<DecIn: _parity_scale_codec::Input>(
				input: &mut DecIn,
			) -> core::result::Result<Self, _parity_scale_codec::Error> {
				Ok(RawSolution {
					winners: {
						let res = _parity_scale_codec::Decode::decode(input);
						match res {
							Err(_) => return Err("Error decoding field RawSolution.winners".into()),
							Ok(a) => a,
						}
					},
					compact: {
						let res = _parity_scale_codec::Decode::decode(input);
						match res {
							Err(_) => return Err("Error decoding field RawSolution.compact".into()),
							Ok(a) => a,
						}
					},
					score: {
						let res = _parity_scale_codec::Decode::decode(input);
						match res {
							Err(_) => return Err("Error decoding field RawSolution.score".into()),
							Ok(a) => a,
						}
					},
				})
			}
		}
	};
	impl core::fmt::Debug for RawSolution {
		fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
			fmt.debug_struct("RawSolution")
				.field("winners", &self.winners)
				.field("compact", &self.compact)
				.field("score", &self.score)
				.finish()
		}
	}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl ::core::default::Default for RawSolution {
		#[inline]
		fn default() -> RawSolution {
			RawSolution {
				winners: ::core::default::Default::default(),
				compact: ::core::default::Default::default(),
				score: ::core::default::Default::default(),
			}
		}
	}
	pub struct SignedSubmission<AccountId, Balance: HasCompact> {
		who: AccountId,
		deposit: Balance,
		reward: Balance,
		solution: RawSolution,
	}
	impl<AccountId, Balance: HasCompact> ::core::marker::StructuralPartialEq
		for SignedSubmission<AccountId, Balance>
	{
	}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<AccountId: ::core::cmp::PartialEq, Balance: ::core::cmp::PartialEq + HasCompact>
		::core::cmp::PartialEq for SignedSubmission<AccountId, Balance>
	{
		#[inline]
		fn eq(&self, other: &SignedSubmission<AccountId, Balance>) -> bool {
			match *other {
				SignedSubmission {
					who: ref __self_1_0,
					deposit: ref __self_1_1,
					reward: ref __self_1_2,
					solution: ref __self_1_3,
				} => match *self {
					SignedSubmission {
						who: ref __self_0_0,
						deposit: ref __self_0_1,
						reward: ref __self_0_2,
						solution: ref __self_0_3,
					} => {
						(*__self_0_0) == (*__self_1_0)
							&& (*__self_0_1) == (*__self_1_1)
							&& (*__self_0_2) == (*__self_1_2)
							&& (*__self_0_3) == (*__self_1_3)
					}
				},
			}
		}
		#[inline]
		fn ne(&self, other: &SignedSubmission<AccountId, Balance>) -> bool {
			match *other {
				SignedSubmission {
					who: ref __self_1_0,
					deposit: ref __self_1_1,
					reward: ref __self_1_2,
					solution: ref __self_1_3,
				} => match *self {
					SignedSubmission {
						who: ref __self_0_0,
						deposit: ref __self_0_1,
						reward: ref __self_0_2,
						solution: ref __self_0_3,
					} => {
						(*__self_0_0) != (*__self_1_0)
							|| (*__self_0_1) != (*__self_1_1)
							|| (*__self_0_2) != (*__self_1_2)
							|| (*__self_0_3) != (*__self_1_3)
					}
				},
			}
		}
	}
	impl<AccountId, Balance: HasCompact> ::core::marker::StructuralEq
		for SignedSubmission<AccountId, Balance>
	{
	}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<AccountId: ::core::cmp::Eq, Balance: ::core::cmp::Eq + HasCompact> ::core::cmp::Eq
		for SignedSubmission<AccountId, Balance>
	{
		#[inline]
		#[doc(hidden)]
		fn assert_receiver_is_total_eq(&self) -> () {
			{
				let _: ::core::cmp::AssertParamIsEq<AccountId>;
				let _: ::core::cmp::AssertParamIsEq<Balance>;
				let _: ::core::cmp::AssertParamIsEq<Balance>;
				let _: ::core::cmp::AssertParamIsEq<RawSolution>;
			}
		}
	}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<AccountId: ::core::clone::Clone, Balance: ::core::clone::Clone + HasCompact>
		::core::clone::Clone for SignedSubmission<AccountId, Balance>
	{
		#[inline]
		fn clone(&self) -> SignedSubmission<AccountId, Balance> {
			match *self {
				SignedSubmission {
					who: ref __self_0_0,
					deposit: ref __self_0_1,
					reward: ref __self_0_2,
					solution: ref __self_0_3,
				} => SignedSubmission {
					who: ::core::clone::Clone::clone(&(*__self_0_0)),
					deposit: ::core::clone::Clone::clone(&(*__self_0_1)),
					reward: ::core::clone::Clone::clone(&(*__self_0_2)),
					solution: ::core::clone::Clone::clone(&(*__self_0_3)),
				},
			}
		}
	}
	const _: () = {
		#[allow(unknown_lints)]
		#[allow(rust_2018_idioms)]
		extern crate codec as _parity_scale_codec;
		impl<AccountId, Balance: HasCompact> _parity_scale_codec::Encode
			for SignedSubmission<AccountId, Balance>
		where
			AccountId: _parity_scale_codec::Encode,
			AccountId: _parity_scale_codec::Encode,
			Balance: _parity_scale_codec::Encode,
			Balance: _parity_scale_codec::Encode,
			Balance: _parity_scale_codec::Encode,
			Balance: _parity_scale_codec::Encode,
		{
			fn encode_to<EncOut: _parity_scale_codec::Output>(&self, dest: &mut EncOut) {
				dest.push(&self.who);
				dest.push(&self.deposit);
				dest.push(&self.reward);
				dest.push(&self.solution);
			}
		}
		impl<AccountId, Balance: HasCompact> _parity_scale_codec::EncodeLike
			for SignedSubmission<AccountId, Balance>
		where
			AccountId: _parity_scale_codec::Encode,
			AccountId: _parity_scale_codec::Encode,
			Balance: _parity_scale_codec::Encode,
			Balance: _parity_scale_codec::Encode,
			Balance: _parity_scale_codec::Encode,
			Balance: _parity_scale_codec::Encode,
		{
		}
	};
	const _: () = {
		#[allow(unknown_lints)]
		#[allow(rust_2018_idioms)]
		extern crate codec as _parity_scale_codec;
		impl<AccountId, Balance: HasCompact> _parity_scale_codec::Decode
			for SignedSubmission<AccountId, Balance>
		where
			AccountId: _parity_scale_codec::Decode,
			AccountId: _parity_scale_codec::Decode,
			Balance: _parity_scale_codec::Decode,
			Balance: _parity_scale_codec::Decode,
			Balance: _parity_scale_codec::Decode,
			Balance: _parity_scale_codec::Decode,
		{
			fn decode<DecIn: _parity_scale_codec::Input>(
				input: &mut DecIn,
			) -> core::result::Result<Self, _parity_scale_codec::Error> {
				Ok(SignedSubmission {
					who: {
						let res = _parity_scale_codec::Decode::decode(input);
						match res {
							Err(_) => {
								return Err("Error decoding field SignedSubmission.who".into())
							}
							Ok(a) => a,
						}
					},
					deposit: {
						let res = _parity_scale_codec::Decode::decode(input);
						match res {
							Err(_) => {
								return Err("Error decoding field SignedSubmission.deposit".into())
							}
							Ok(a) => a,
						}
					},
					reward: {
						let res = _parity_scale_codec::Decode::decode(input);
						match res {
							Err(_) => {
								return Err("Error decoding field SignedSubmission.reward".into())
							}
							Ok(a) => a,
						}
					},
					solution: {
						let res = _parity_scale_codec::Decode::decode(input);
						match res {
							Err(_) => {
								return Err("Error decoding field SignedSubmission.solution".into())
							}
							Ok(a) => a,
						}
					},
				})
			}
		}
	};
	impl<AccountId, Balance: HasCompact> core::fmt::Debug for SignedSubmission<AccountId, Balance>
	where
		AccountId: core::fmt::Debug,
		Balance: core::fmt::Debug,
	{
		fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
			fmt.debug_struct("SignedSubmission")
				.field("who", &self.who)
				.field("deposit", &self.deposit)
				.field("reward", &self.reward)
				.field("solution", &self.solution)
				.finish()
		}
	}
	/// A parsed solution, ready to be enacted.
	pub struct ReadySolution<AccountId> {
		winners: Vec<AccountId>,
		supports: FlatSupportMap<AccountId>,
		compute: ElectionCompute,
	}
	impl<AccountId> ::core::marker::StructuralPartialEq for ReadySolution<AccountId> {}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<AccountId: ::core::cmp::PartialEq> ::core::cmp::PartialEq for ReadySolution<AccountId> {
		#[inline]
		fn eq(&self, other: &ReadySolution<AccountId>) -> bool {
			match *other {
				ReadySolution {
					winners: ref __self_1_0,
					supports: ref __self_1_1,
					compute: ref __self_1_2,
				} => match *self {
					ReadySolution {
						winners: ref __self_0_0,
						supports: ref __self_0_1,
						compute: ref __self_0_2,
					} => {
						(*__self_0_0) == (*__self_1_0)
							&& (*__self_0_1) == (*__self_1_1)
							&& (*__self_0_2) == (*__self_1_2)
					}
				},
			}
		}
		#[inline]
		fn ne(&self, other: &ReadySolution<AccountId>) -> bool {
			match *other {
				ReadySolution {
					winners: ref __self_1_0,
					supports: ref __self_1_1,
					compute: ref __self_1_2,
				} => match *self {
					ReadySolution {
						winners: ref __self_0_0,
						supports: ref __self_0_1,
						compute: ref __self_0_2,
					} => {
						(*__self_0_0) != (*__self_1_0)
							|| (*__self_0_1) != (*__self_1_1)
							|| (*__self_0_2) != (*__self_1_2)
					}
				},
			}
		}
	}
	impl<AccountId> ::core::marker::StructuralEq for ReadySolution<AccountId> {}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<AccountId: ::core::cmp::Eq> ::core::cmp::Eq for ReadySolution<AccountId> {
		#[inline]
		#[doc(hidden)]
		fn assert_receiver_is_total_eq(&self) -> () {
			{
				let _: ::core::cmp::AssertParamIsEq<Vec<AccountId>>;
				let _: ::core::cmp::AssertParamIsEq<FlatSupportMap<AccountId>>;
				let _: ::core::cmp::AssertParamIsEq<ElectionCompute>;
			}
		}
	}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<AccountId: ::core::clone::Clone> ::core::clone::Clone for ReadySolution<AccountId> {
		#[inline]
		fn clone(&self) -> ReadySolution<AccountId> {
			match *self {
				ReadySolution {
					winners: ref __self_0_0,
					supports: ref __self_0_1,
					compute: ref __self_0_2,
				} => ReadySolution {
					winners: ::core::clone::Clone::clone(&(*__self_0_0)),
					supports: ::core::clone::Clone::clone(&(*__self_0_1)),
					compute: ::core::clone::Clone::clone(&(*__self_0_2)),
				},
			}
		}
	}
	const _: () = {
		#[allow(unknown_lints)]
		#[allow(rust_2018_idioms)]
		extern crate codec as _parity_scale_codec;
		impl<AccountId> _parity_scale_codec::Encode for ReadySolution<AccountId>
		where
			Vec<AccountId>: _parity_scale_codec::Encode,
			Vec<AccountId>: _parity_scale_codec::Encode,
			FlatSupportMap<AccountId>: _parity_scale_codec::Encode,
			FlatSupportMap<AccountId>: _parity_scale_codec::Encode,
		{
			fn encode_to<EncOut: _parity_scale_codec::Output>(&self, dest: &mut EncOut) {
				dest.push(&self.winners);
				dest.push(&self.supports);
				dest.push(&self.compute);
			}
		}
		impl<AccountId> _parity_scale_codec::EncodeLike for ReadySolution<AccountId>
		where
			Vec<AccountId>: _parity_scale_codec::Encode,
			Vec<AccountId>: _parity_scale_codec::Encode,
			FlatSupportMap<AccountId>: _parity_scale_codec::Encode,
			FlatSupportMap<AccountId>: _parity_scale_codec::Encode,
		{
		}
	};
	const _: () = {
		#[allow(unknown_lints)]
		#[allow(rust_2018_idioms)]
		extern crate codec as _parity_scale_codec;
		impl<AccountId> _parity_scale_codec::Decode for ReadySolution<AccountId>
		where
			Vec<AccountId>: _parity_scale_codec::Decode,
			Vec<AccountId>: _parity_scale_codec::Decode,
			FlatSupportMap<AccountId>: _parity_scale_codec::Decode,
			FlatSupportMap<AccountId>: _parity_scale_codec::Decode,
		{
			fn decode<DecIn: _parity_scale_codec::Input>(
				input: &mut DecIn,
			) -> core::result::Result<Self, _parity_scale_codec::Error> {
				Ok(ReadySolution {
					winners: {
						let res = _parity_scale_codec::Decode::decode(input);
						match res {
							Err(_) => {
								return Err("Error decoding field ReadySolution.winners".into())
							}
							Ok(a) => a,
						}
					},
					supports: {
						let res = _parity_scale_codec::Decode::decode(input);
						match res {
							Err(_) => {
								return Err("Error decoding field ReadySolution.supports".into())
							}
							Ok(a) => a,
						}
					},
					compute: {
						let res = _parity_scale_codec::Decode::decode(input);
						match res {
							Err(_) => {
								return Err("Error decoding field ReadySolution.compute".into())
							}
							Ok(a) => a,
						}
					},
				})
			}
		}
	};
	impl<AccountId> core::fmt::Debug for ReadySolution<AccountId>
	where
		AccountId: core::fmt::Debug,
	{
		fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
			fmt.debug_struct("ReadySolution")
				.field("winners", &self.winners)
				.field("supports", &self.supports)
				.field("compute", &self.compute)
				.finish()
		}
	}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<AccountId: ::core::default::Default> ::core::default::Default for ReadySolution<AccountId> {
		#[inline]
		fn default() -> ReadySolution<AccountId> {
			ReadySolution {
				winners: ::core::default::Default::default(),
				supports: ::core::default::Default::default(),
				compute: ::core::default::Default::default(),
			}
		}
	}
	pub trait WeightInfo {}
	impl WeightInfo for () {}
	pub trait Trait: frame_system::Trait {
		type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
		type Currency: ReservableCurrency<Self::AccountId> + Currency<Self::AccountId>;
		type SignedPhase: Get<Self::BlockNumber>;
		type UnsignedPhase: Get<Self::BlockNumber>;
		type MaxSignedSubmissions: Get<u32>;
		type SignedRewardBase: Get<BalanceOf<Self>>;
		type SignedRewardFactor: Get<Perbill>;
		type SignedDepositBase: Get<BalanceOf<Self>>;
		type SignedDepositByte: Get<BalanceOf<Self>>;
		type SignedDepositWeight: Get<BalanceOf<Self>>;
		type SolutionImprovementThreshold: Get<Perbill>;
		type SlashHandler: OnUnbalanced<NegativeImbalanceOf<Self>>;
		type RewardHandler: OnUnbalanced<PositiveImbalanceOf<Self>>;
		type ElectionDataProvider: ElectionDataProvider<Self::AccountId, Self::BlockNumber>;
		type WeightInfo: WeightInfo;
	}
	use self::sp_api_hidden_includes_decl_storage::hidden_include::{
		IterableStorageDoubleMap as _, IterableStorageMap as _, StorageDoubleMap as _,
		StorageMap as _, StoragePrefixedMap as _, StorageValue as _,
	};
	#[doc(hidden)]
	mod sp_api_hidden_includes_decl_storage {
		pub extern crate frame_support as hidden_include;
	}
	trait Store {
		type CurrentPhase;
		type SignedSubmissions;
		type QueuedSolution;
		type SnapshotTargets;
		type SnapshotVoters;
		type DesiredTargets;
	}
	impl<T: Trait + 'static> Store for Module<T> {
		type CurrentPhase = CurrentPhase;
		type SignedSubmissions = SignedSubmissions<T>;
		type QueuedSolution = QueuedSolution<T>;
		type SnapshotTargets = SnapshotTargets<T>;
		type SnapshotVoters = SnapshotVoters<T>;
		type DesiredTargets = DesiredTargets;
	}
	impl<T: Trait + 'static> Module<T> {
		/// Current phase.
		pub fn current_phase() -> Phase {
			< CurrentPhase < > as self :: sp_api_hidden_includes_decl_storage :: hidden_include :: storage :: StorageValue < Phase > > :: get ( )
		}
		/// Sorted list of unchecked, signed solutions.
		pub fn signed_submissions() -> Vec<SignedSubmission<T::AccountId, BalanceOf<T>>> {
			< SignedSubmissions < T > as self :: sp_api_hidden_includes_decl_storage :: hidden_include :: storage :: StorageValue < Vec < SignedSubmission < T :: AccountId , BalanceOf < T > > > > > :: get ( )
		}
		/// Current, best, unsigned solution.
		pub fn queued_solution() -> Option<ReadySolution<T::AccountId>> {
			< QueuedSolution < T > as self :: sp_api_hidden_includes_decl_storage :: hidden_include :: storage :: StorageValue < ReadySolution < T :: AccountId > > > :: get ( )
		}
		/// Snapshot of all Voters. The indices if this will be used in election.
		///
		/// This is created at the beginning of the signed phase and cleared upon calling `elect`.
		pub fn snapshot_targets() -> Option<Vec<T::AccountId>> {
			< SnapshotTargets < T > as self :: sp_api_hidden_includes_decl_storage :: hidden_include :: storage :: StorageValue < Vec < T :: AccountId > > > :: get ( )
		}
		/// Snapshot of all targets. The indices if this will be used in election.
		///
		/// This is created at the beginning of the signed phase and cleared upon calling `elect`.
		pub fn snapshot_voters() -> Option<Vec<(T::AccountId, VoteWeight, Vec<T::AccountId>)>> {
			< SnapshotVoters < T > as self :: sp_api_hidden_includes_decl_storage :: hidden_include :: storage :: StorageValue < Vec < ( T :: AccountId , VoteWeight , Vec < T :: AccountId > ) > > > :: get ( )
		}
		/// Desired number of targets to elect
		pub fn desired_targets() -> u32 {
			< DesiredTargets < > as self :: sp_api_hidden_includes_decl_storage :: hidden_include :: storage :: StorageValue < u32 > > :: get ( )
		}
	}
	#[doc(hidden)]
	pub struct __GetByteStructCurrentPhase<T>(
		pub  self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::marker::PhantomData<
			(T),
		>,
	);
	#[cfg(feature = "std")]
	#[allow(non_upper_case_globals)]
	static __CACHE_GET_BYTE_STRUCT_CurrentPhase:
		self::sp_api_hidden_includes_decl_storage::hidden_include::once_cell::sync::OnceCell<
			self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::vec::Vec<u8>,
		> = self::sp_api_hidden_includes_decl_storage::hidden_include::once_cell::sync::OnceCell::new();
	#[cfg(feature = "std")]
	impl<T: Trait> self::sp_api_hidden_includes_decl_storage::hidden_include::metadata::DefaultByte
		for __GetByteStructCurrentPhase<T>
	{
		fn default_byte(
			&self,
		) -> self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::vec::Vec<u8> {
			use self::sp_api_hidden_includes_decl_storage::hidden_include::codec::Encode;
			__CACHE_GET_BYTE_STRUCT_CurrentPhase
				.get_or_init(|| {
					let def_val: Phase = Phase::Off;
					<Phase as Encode>::encode(&def_val)
				})
				.clone()
		}
	}
	unsafe impl<T: Trait> Send for __GetByteStructCurrentPhase<T> {}
	unsafe impl<T: Trait> Sync for __GetByteStructCurrentPhase<T> {}
	#[doc(hidden)]
	pub struct __GetByteStructSignedSubmissions<T>(
		pub  self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::marker::PhantomData<
			(T),
		>,
	);
	#[cfg(feature = "std")]
	#[allow(non_upper_case_globals)]
	static __CACHE_GET_BYTE_STRUCT_SignedSubmissions:
		self::sp_api_hidden_includes_decl_storage::hidden_include::once_cell::sync::OnceCell<
			self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::vec::Vec<u8>,
		> = self::sp_api_hidden_includes_decl_storage::hidden_include::once_cell::sync::OnceCell::new();
	#[cfg(feature = "std")]
	impl<T: Trait> self::sp_api_hidden_includes_decl_storage::hidden_include::metadata::DefaultByte
		for __GetByteStructSignedSubmissions<T>
	{
		fn default_byte(
			&self,
		) -> self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::vec::Vec<u8> {
			use self::sp_api_hidden_includes_decl_storage::hidden_include::codec::Encode;
			__CACHE_GET_BYTE_STRUCT_SignedSubmissions
				.get_or_init(|| {
					let def_val: Vec<SignedSubmission<T::AccountId, BalanceOf<T>>> =
						Default::default();
					<Vec<SignedSubmission<T::AccountId, BalanceOf<T>>> as Encode>::encode(&def_val)
				})
				.clone()
		}
	}
	unsafe impl<T: Trait> Send for __GetByteStructSignedSubmissions<T> {}
	unsafe impl<T: Trait> Sync for __GetByteStructSignedSubmissions<T> {}
	#[doc(hidden)]
	pub struct __GetByteStructQueuedSolution<T>(
		pub  self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::marker::PhantomData<
			(T),
		>,
	);
	#[cfg(feature = "std")]
	#[allow(non_upper_case_globals)]
	static __CACHE_GET_BYTE_STRUCT_QueuedSolution:
		self::sp_api_hidden_includes_decl_storage::hidden_include::once_cell::sync::OnceCell<
			self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::vec::Vec<u8>,
		> = self::sp_api_hidden_includes_decl_storage::hidden_include::once_cell::sync::OnceCell::new();
	#[cfg(feature = "std")]
	impl<T: Trait> self::sp_api_hidden_includes_decl_storage::hidden_include::metadata::DefaultByte
		for __GetByteStructQueuedSolution<T>
	{
		fn default_byte(
			&self,
		) -> self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::vec::Vec<u8> {
			use self::sp_api_hidden_includes_decl_storage::hidden_include::codec::Encode;
			__CACHE_GET_BYTE_STRUCT_QueuedSolution
				.get_or_init(|| {
					let def_val: Option<ReadySolution<T::AccountId>> = Default::default();
					<Option<ReadySolution<T::AccountId>> as Encode>::encode(&def_val)
				})
				.clone()
		}
	}
	unsafe impl<T: Trait> Send for __GetByteStructQueuedSolution<T> {}
	unsafe impl<T: Trait> Sync for __GetByteStructQueuedSolution<T> {}
	#[doc(hidden)]
	pub struct __GetByteStructSnapshotTargets<T>(
		pub  self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::marker::PhantomData<
			(T),
		>,
	);
	#[cfg(feature = "std")]
	#[allow(non_upper_case_globals)]
	static __CACHE_GET_BYTE_STRUCT_SnapshotTargets:
		self::sp_api_hidden_includes_decl_storage::hidden_include::once_cell::sync::OnceCell<
			self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::vec::Vec<u8>,
		> = self::sp_api_hidden_includes_decl_storage::hidden_include::once_cell::sync::OnceCell::new();
	#[cfg(feature = "std")]
	impl<T: Trait> self::sp_api_hidden_includes_decl_storage::hidden_include::metadata::DefaultByte
		for __GetByteStructSnapshotTargets<T>
	{
		fn default_byte(
			&self,
		) -> self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::vec::Vec<u8> {
			use self::sp_api_hidden_includes_decl_storage::hidden_include::codec::Encode;
			__CACHE_GET_BYTE_STRUCT_SnapshotTargets
				.get_or_init(|| {
					let def_val: Option<Vec<T::AccountId>> = Default::default();
					<Option<Vec<T::AccountId>> as Encode>::encode(&def_val)
				})
				.clone()
		}
	}
	unsafe impl<T: Trait> Send for __GetByteStructSnapshotTargets<T> {}
	unsafe impl<T: Trait> Sync for __GetByteStructSnapshotTargets<T> {}
	#[doc(hidden)]
	pub struct __GetByteStructSnapshotVoters<T>(
		pub  self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::marker::PhantomData<
			(T),
		>,
	);
	#[cfg(feature = "std")]
	#[allow(non_upper_case_globals)]
	static __CACHE_GET_BYTE_STRUCT_SnapshotVoters:
		self::sp_api_hidden_includes_decl_storage::hidden_include::once_cell::sync::OnceCell<
			self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::vec::Vec<u8>,
		> = self::sp_api_hidden_includes_decl_storage::hidden_include::once_cell::sync::OnceCell::new();
	#[cfg(feature = "std")]
	impl<T: Trait> self::sp_api_hidden_includes_decl_storage::hidden_include::metadata::DefaultByte
		for __GetByteStructSnapshotVoters<T>
	{
		fn default_byte(
			&self,
		) -> self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::vec::Vec<u8> {
			use self::sp_api_hidden_includes_decl_storage::hidden_include::codec::Encode;
			__CACHE_GET_BYTE_STRUCT_SnapshotVoters
				.get_or_init(|| {
					let def_val: Option<Vec<(T::AccountId, VoteWeight, Vec<T::AccountId>)>> =
						Default::default();
					<Option<Vec<(T::AccountId, VoteWeight, Vec<T::AccountId>)>> as Encode>::encode(
						&def_val,
					)
				})
				.clone()
		}
	}
	unsafe impl<T: Trait> Send for __GetByteStructSnapshotVoters<T> {}
	unsafe impl<T: Trait> Sync for __GetByteStructSnapshotVoters<T> {}
	#[doc(hidden)]
	pub struct __GetByteStructDesiredTargets<T>(
		pub  self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::marker::PhantomData<
			(T),
		>,
	);
	#[cfg(feature = "std")]
	#[allow(non_upper_case_globals)]
	static __CACHE_GET_BYTE_STRUCT_DesiredTargets:
		self::sp_api_hidden_includes_decl_storage::hidden_include::once_cell::sync::OnceCell<
			self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::vec::Vec<u8>,
		> = self::sp_api_hidden_includes_decl_storage::hidden_include::once_cell::sync::OnceCell::new();
	#[cfg(feature = "std")]
	impl<T: Trait> self::sp_api_hidden_includes_decl_storage::hidden_include::metadata::DefaultByte
		for __GetByteStructDesiredTargets<T>
	{
		fn default_byte(
			&self,
		) -> self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::vec::Vec<u8> {
			use self::sp_api_hidden_includes_decl_storage::hidden_include::codec::Encode;
			__CACHE_GET_BYTE_STRUCT_DesiredTargets
				.get_or_init(|| {
					let def_val: u32 = Default::default();
					<u32 as Encode>::encode(&def_val)
				})
				.clone()
		}
	}
	unsafe impl<T: Trait> Send for __GetByteStructDesiredTargets<T> {}
	unsafe impl<T: Trait> Sync for __GetByteStructDesiredTargets<T> {}
	impl<T: Trait + 'static> Module<T> {
		#[doc(hidden)]
		pub fn storage_metadata(
		) -> self::sp_api_hidden_includes_decl_storage::hidden_include::metadata::StorageMetadata {
			self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageMetadata { prefix : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "TwoPhaseElectionProvider" ) , entries : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( & [ self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryMetadata { name : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "CurrentPhase" ) , modifier : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryModifier :: Default , ty : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryType :: Plain ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "Phase" ) ) , default : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DefaultByteGetter ( & __GetByteStructCurrentPhase :: < T > ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: sp_std :: marker :: PhantomData ) ) ) , documentation : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( & [ " Current phase." ] ) , } , self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryMetadata { name : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "SignedSubmissions" ) , modifier : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryModifier :: Default , ty : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryType :: Plain ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "Vec<SignedSubmission<T::AccountId, BalanceOf<T>>>" ) ) , default : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DefaultByteGetter ( & __GetByteStructSignedSubmissions :: < T > ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: sp_std :: marker :: PhantomData ) ) ) , documentation : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( & [ " Sorted list of unchecked, signed solutions." ] ) , } , self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryMetadata { name : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "QueuedSolution" ) , modifier : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryModifier :: Optional , ty : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryType :: Plain ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "ReadySolution<T::AccountId>" ) ) , default : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DefaultByteGetter ( & __GetByteStructQueuedSolution :: < T > ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: sp_std :: marker :: PhantomData ) ) ) , documentation : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( & [ " Current, best, unsigned solution." ] ) , } , self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryMetadata { name : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "SnapshotTargets" ) , modifier : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryModifier :: Optional , ty : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryType :: Plain ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "Vec<T::AccountId>" ) ) , default : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DefaultByteGetter ( & __GetByteStructSnapshotTargets :: < T > ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: sp_std :: marker :: PhantomData ) ) ) , documentation : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( & [ " Snapshot of all Voters. The indices if this will be used in election." , "" , " This is created at the beginning of the signed phase and cleared upon calling `elect`." ] ) , } , self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryMetadata { name : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "SnapshotVoters" ) , modifier : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryModifier :: Optional , ty : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryType :: Plain ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "Vec<(T::AccountId, VoteWeight, Vec<T::AccountId>)>" ) ) , default : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DefaultByteGetter ( & __GetByteStructSnapshotVoters :: < T > ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: sp_std :: marker :: PhantomData ) ) ) , documentation : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( & [ " Snapshot of all targets. The indices if this will be used in election." , "" , " This is created at the beginning of the signed phase and cleared upon calling `elect`." ] ) , } , self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryMetadata { name : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "DesiredTargets" ) , modifier : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryModifier :: Default , ty : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryType :: Plain ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "u32" ) ) , default : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DefaultByteGetter ( & __GetByteStructDesiredTargets :: < T > ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: sp_std :: marker :: PhantomData ) ) ) , documentation : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( & [ " Desired number of targets to elect" ] ) , } ] [ .. ] ) , }
		}
	}
	/// Hidden instance generated to be internally used when module is used without
	/// instance.
	#[doc(hidden)]
	pub struct __InherentHiddenInstance;
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl ::core::clone::Clone for __InherentHiddenInstance {
		#[inline]
		fn clone(&self) -> __InherentHiddenInstance {
			match *self {
				__InherentHiddenInstance => __InherentHiddenInstance,
			}
		}
	}
	impl ::core::marker::StructuralEq for __InherentHiddenInstance {}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl ::core::cmp::Eq for __InherentHiddenInstance {
		#[inline]
		#[doc(hidden)]
		fn assert_receiver_is_total_eq(&self) -> () {
			{}
		}
	}
	impl ::core::marker::StructuralPartialEq for __InherentHiddenInstance {}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl ::core::cmp::PartialEq for __InherentHiddenInstance {
		#[inline]
		fn eq(&self, other: &__InherentHiddenInstance) -> bool {
			match *other {
				__InherentHiddenInstance => match *self {
					__InherentHiddenInstance => true,
				},
			}
		}
	}
	const _: () = {
		#[allow(unknown_lints)]
		#[allow(rust_2018_idioms)]
		extern crate codec as _parity_scale_codec;
		impl _parity_scale_codec::Encode for __InherentHiddenInstance {
			fn encode_to<EncOut: _parity_scale_codec::Output>(&self, dest: &mut EncOut) {}
		}
		impl _parity_scale_codec::EncodeLike for __InherentHiddenInstance {}
	};
	const _: () = {
		#[allow(unknown_lints)]
		#[allow(rust_2018_idioms)]
		extern crate codec as _parity_scale_codec;
		impl _parity_scale_codec::Decode for __InherentHiddenInstance {
			fn decode<DecIn: _parity_scale_codec::Input>(
				input: &mut DecIn,
			) -> core::result::Result<Self, _parity_scale_codec::Error> {
				Ok(__InherentHiddenInstance)
			}
		}
	};
	impl core::fmt::Debug for __InherentHiddenInstance {
		fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
			fmt.debug_tuple("__InherentHiddenInstance").finish()
		}
	}
	impl self::sp_api_hidden_includes_decl_storage::hidden_include::traits::Instance
		for __InherentHiddenInstance
	{
		const PREFIX: &'static str = "TwoPhaseElectionProvider";
	}
	/// Current phase.
	pub struct CurrentPhase(
		self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::marker::PhantomData<()>,
	);
	impl
		self::sp_api_hidden_includes_decl_storage::hidden_include::storage::generator::StorageValue<
			Phase,
		> for CurrentPhase
	{
		type Query = Phase;
		fn module_prefix() -> &'static [u8] {
			< __InherentHiddenInstance as self :: sp_api_hidden_includes_decl_storage :: hidden_include :: traits :: Instance > :: PREFIX . as_bytes ( )
		}
		fn storage_prefix() -> &'static [u8] {
			b"CurrentPhase"
		}
		fn from_optional_value_to_query(v: Option<Phase>) -> Self::Query {
			v.unwrap_or_else(|| Phase::Off)
		}
		fn from_query_to_optional_value(v: Self::Query) -> Option<Phase> {
			Some(v)
		}
	}
	/// Sorted list of unchecked, signed solutions.
	pub struct SignedSubmissions<T: Trait>(
		self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::marker::PhantomData<
				(T,),
			>,
	);
	impl<T: Trait>
		self::sp_api_hidden_includes_decl_storage::hidden_include::storage::generator::StorageValue<
			Vec<SignedSubmission<T::AccountId, BalanceOf<T>>>,
		> for SignedSubmissions<T>
	{
		type Query = Vec<SignedSubmission<T::AccountId, BalanceOf<T>>>;
		fn module_prefix() -> &'static [u8] {
			< __InherentHiddenInstance as self :: sp_api_hidden_includes_decl_storage :: hidden_include :: traits :: Instance > :: PREFIX . as_bytes ( )
		}
		fn storage_prefix() -> &'static [u8] {
			b"SignedSubmissions"
		}
		fn from_optional_value_to_query(
			v: Option<Vec<SignedSubmission<T::AccountId, BalanceOf<T>>>>,
		) -> Self::Query {
			v.unwrap_or_else(|| Default::default())
		}
		fn from_query_to_optional_value(
			v: Self::Query,
		) -> Option<Vec<SignedSubmission<T::AccountId, BalanceOf<T>>>> {
			Some(v)
		}
	}
	/// Current, best, unsigned solution.
	pub struct QueuedSolution<T: Trait>(
		self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::marker::PhantomData<
				(T,),
			>,
	);
	impl<T: Trait>
		self::sp_api_hidden_includes_decl_storage::hidden_include::storage::generator::StorageValue<
			ReadySolution<T::AccountId>,
		> for QueuedSolution<T>
	{
		type Query = Option<ReadySolution<T::AccountId>>;
		fn module_prefix() -> &'static [u8] {
			< __InherentHiddenInstance as self :: sp_api_hidden_includes_decl_storage :: hidden_include :: traits :: Instance > :: PREFIX . as_bytes ( )
		}
		fn storage_prefix() -> &'static [u8] {
			b"QueuedSolution"
		}
		fn from_optional_value_to_query(v: Option<ReadySolution<T::AccountId>>) -> Self::Query {
			v.or_else(|| Default::default())
		}
		fn from_query_to_optional_value(v: Self::Query) -> Option<ReadySolution<T::AccountId>> {
			v
		}
	}
	/// Snapshot of all Voters. The indices if this will be used in election.
	///
	/// This is created at the beginning of the signed phase and cleared upon calling `elect`.
	pub struct SnapshotTargets<T: Trait>(
		self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::marker::PhantomData<
				(T,),
			>,
	);
	impl<T: Trait>
		self::sp_api_hidden_includes_decl_storage::hidden_include::storage::generator::StorageValue<
			Vec<T::AccountId>,
		> for SnapshotTargets<T>
	{
		type Query = Option<Vec<T::AccountId>>;
		fn module_prefix() -> &'static [u8] {
			< __InherentHiddenInstance as self :: sp_api_hidden_includes_decl_storage :: hidden_include :: traits :: Instance > :: PREFIX . as_bytes ( )
		}
		fn storage_prefix() -> &'static [u8] {
			b"SnapshotTargets"
		}
		fn from_optional_value_to_query(v: Option<Vec<T::AccountId>>) -> Self::Query {
			v.or_else(|| Default::default())
		}
		fn from_query_to_optional_value(v: Self::Query) -> Option<Vec<T::AccountId>> {
			v
		}
	}
	/// Snapshot of all targets. The indices if this will be used in election.
	///
	/// This is created at the beginning of the signed phase and cleared upon calling `elect`.
	pub struct SnapshotVoters<T: Trait>(
		self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::marker::PhantomData<
				(T,),
			>,
	);
	impl<T: Trait>
		self::sp_api_hidden_includes_decl_storage::hidden_include::storage::generator::StorageValue<
			Vec<(T::AccountId, VoteWeight, Vec<T::AccountId>)>,
		> for SnapshotVoters<T>
	{
		type Query = Option<Vec<(T::AccountId, VoteWeight, Vec<T::AccountId>)>>;
		fn module_prefix() -> &'static [u8] {
			< __InherentHiddenInstance as self :: sp_api_hidden_includes_decl_storage :: hidden_include :: traits :: Instance > :: PREFIX . as_bytes ( )
		}
		fn storage_prefix() -> &'static [u8] {
			b"SnapshotVoters"
		}
		fn from_optional_value_to_query(
			v: Option<Vec<(T::AccountId, VoteWeight, Vec<T::AccountId>)>>,
		) -> Self::Query {
			v.or_else(|| Default::default())
		}
		fn from_query_to_optional_value(
			v: Self::Query,
		) -> Option<Vec<(T::AccountId, VoteWeight, Vec<T::AccountId>)>> {
			v
		}
	}
	/// Desired number of targets to elect
	pub struct DesiredTargets(
		self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::marker::PhantomData<()>,
	);
	impl
		self::sp_api_hidden_includes_decl_storage::hidden_include::storage::generator::StorageValue<
			u32,
		> for DesiredTargets
	{
		type Query = u32;
		fn module_prefix() -> &'static [u8] {
			< __InherentHiddenInstance as self :: sp_api_hidden_includes_decl_storage :: hidden_include :: traits :: Instance > :: PREFIX . as_bytes ( )
		}
		fn storage_prefix() -> &'static [u8] {
			b"DesiredTargets"
		}
		fn from_optional_value_to_query(v: Option<u32>) -> Self::Query {
			v.unwrap_or_else(|| Default::default())
		}
		fn from_query_to_optional_value(v: Self::Query) -> Option<u32> {
			Some(v)
		}
	}
	/// [`RawEvent`] specialized for the configuration [`Trait`]
	///
	/// [`RawEvent`]: enum.RawEvent.html
	/// [`Trait`]: trait.Trait.html
	pub type Event<T> = RawEvent<<T as frame_system::Trait>::AccountId>;
	/// Events for this module.
	///
	pub enum RawEvent<AccountId> {
		/// A solution was sot
		SolutionStored(ElectionCompute),
		ElectionFinalized(Option<ElectionCompute>),
		Rewarded(AccountId),
		Slashed(AccountId),
	}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<AccountId: ::core::clone::Clone> ::core::clone::Clone for RawEvent<AccountId> {
		#[inline]
		fn clone(&self) -> RawEvent<AccountId> {
			match (&*self,) {
				(&RawEvent::SolutionStored(ref __self_0),) => {
					RawEvent::SolutionStored(::core::clone::Clone::clone(&(*__self_0)))
				}
				(&RawEvent::ElectionFinalized(ref __self_0),) => {
					RawEvent::ElectionFinalized(::core::clone::Clone::clone(&(*__self_0)))
				}
				(&RawEvent::Rewarded(ref __self_0),) => {
					RawEvent::Rewarded(::core::clone::Clone::clone(&(*__self_0)))
				}
				(&RawEvent::Slashed(ref __self_0),) => {
					RawEvent::Slashed(::core::clone::Clone::clone(&(*__self_0)))
				}
			}
		}
	}
	impl<AccountId> ::core::marker::StructuralPartialEq for RawEvent<AccountId> {}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<AccountId: ::core::cmp::PartialEq> ::core::cmp::PartialEq for RawEvent<AccountId> {
		#[inline]
		fn eq(&self, other: &RawEvent<AccountId>) -> bool {
			{
				let __self_vi = unsafe { ::core::intrinsics::discriminant_value(&*self) };
				let __arg_1_vi = unsafe { ::core::intrinsics::discriminant_value(&*other) };
				if true && __self_vi == __arg_1_vi {
					match (&*self, &*other) {
						(
							&RawEvent::SolutionStored(ref __self_0),
							&RawEvent::SolutionStored(ref __arg_1_0),
						) => (*__self_0) == (*__arg_1_0),
						(
							&RawEvent::ElectionFinalized(ref __self_0),
							&RawEvent::ElectionFinalized(ref __arg_1_0),
						) => (*__self_0) == (*__arg_1_0),
						(&RawEvent::Rewarded(ref __self_0), &RawEvent::Rewarded(ref __arg_1_0)) => {
							(*__self_0) == (*__arg_1_0)
						}
						(&RawEvent::Slashed(ref __self_0), &RawEvent::Slashed(ref __arg_1_0)) => {
							(*__self_0) == (*__arg_1_0)
						}
						_ => unsafe { ::core::intrinsics::unreachable() },
					}
				} else {
					false
				}
			}
		}
		#[inline]
		fn ne(&self, other: &RawEvent<AccountId>) -> bool {
			{
				let __self_vi = unsafe { ::core::intrinsics::discriminant_value(&*self) };
				let __arg_1_vi = unsafe { ::core::intrinsics::discriminant_value(&*other) };
				if true && __self_vi == __arg_1_vi {
					match (&*self, &*other) {
						(
							&RawEvent::SolutionStored(ref __self_0),
							&RawEvent::SolutionStored(ref __arg_1_0),
						) => (*__self_0) != (*__arg_1_0),
						(
							&RawEvent::ElectionFinalized(ref __self_0),
							&RawEvent::ElectionFinalized(ref __arg_1_0),
						) => (*__self_0) != (*__arg_1_0),
						(&RawEvent::Rewarded(ref __self_0), &RawEvent::Rewarded(ref __arg_1_0)) => {
							(*__self_0) != (*__arg_1_0)
						}
						(&RawEvent::Slashed(ref __self_0), &RawEvent::Slashed(ref __arg_1_0)) => {
							(*__self_0) != (*__arg_1_0)
						}
						_ => unsafe { ::core::intrinsics::unreachable() },
					}
				} else {
					true
				}
			}
		}
	}
	impl<AccountId> ::core::marker::StructuralEq for RawEvent<AccountId> {}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<AccountId: ::core::cmp::Eq> ::core::cmp::Eq for RawEvent<AccountId> {
		#[inline]
		#[doc(hidden)]
		fn assert_receiver_is_total_eq(&self) -> () {
			{
				let _: ::core::cmp::AssertParamIsEq<ElectionCompute>;
				let _: ::core::cmp::AssertParamIsEq<Option<ElectionCompute>>;
				let _: ::core::cmp::AssertParamIsEq<AccountId>;
				let _: ::core::cmp::AssertParamIsEq<AccountId>;
			}
		}
	}
	const _: () = {
		#[allow(unknown_lints)]
		#[allow(rust_2018_idioms)]
		extern crate codec as _parity_scale_codec;
		impl<AccountId> _parity_scale_codec::Encode for RawEvent<AccountId>
		where
			AccountId: _parity_scale_codec::Encode,
			AccountId: _parity_scale_codec::Encode,
			AccountId: _parity_scale_codec::Encode,
			AccountId: _parity_scale_codec::Encode,
		{
			fn encode_to<EncOut: _parity_scale_codec::Output>(&self, dest: &mut EncOut) {
				match *self {
					RawEvent::SolutionStored(ref aa) => {
						dest.push_byte(0usize as u8);
						dest.push(aa);
					}
					RawEvent::ElectionFinalized(ref aa) => {
						dest.push_byte(1usize as u8);
						dest.push(aa);
					}
					RawEvent::Rewarded(ref aa) => {
						dest.push_byte(2usize as u8);
						dest.push(aa);
					}
					RawEvent::Slashed(ref aa) => {
						dest.push_byte(3usize as u8);
						dest.push(aa);
					}
					_ => (),
				}
			}
		}
		impl<AccountId> _parity_scale_codec::EncodeLike for RawEvent<AccountId>
		where
			AccountId: _parity_scale_codec::Encode,
			AccountId: _parity_scale_codec::Encode,
			AccountId: _parity_scale_codec::Encode,
			AccountId: _parity_scale_codec::Encode,
		{
		}
	};
	const _: () = {
		#[allow(unknown_lints)]
		#[allow(rust_2018_idioms)]
		extern crate codec as _parity_scale_codec;
		impl<AccountId> _parity_scale_codec::Decode for RawEvent<AccountId>
		where
			AccountId: _parity_scale_codec::Decode,
			AccountId: _parity_scale_codec::Decode,
			AccountId: _parity_scale_codec::Decode,
			AccountId: _parity_scale_codec::Decode,
		{
			fn decode<DecIn: _parity_scale_codec::Input>(
				input: &mut DecIn,
			) -> core::result::Result<Self, _parity_scale_codec::Error> {
				match input.read_byte()? {
					x if x == 0usize as u8 => Ok(RawEvent::SolutionStored({
						let res = _parity_scale_codec::Decode::decode(input);
						match res {
							Err(_) => {
								return Err(
									"Error decoding field RawEvent :: SolutionStored.0".into()
								)
							}
							Ok(a) => a,
						}
					})),
					x if x == 1usize as u8 => Ok(RawEvent::ElectionFinalized({
						let res = _parity_scale_codec::Decode::decode(input);
						match res {
							Err(_) => {
								return Err(
									"Error decoding field RawEvent :: ElectionFinalized.0".into()
								)
							}
							Ok(a) => a,
						}
					})),
					x if x == 2usize as u8 => Ok(RawEvent::Rewarded({
						let res = _parity_scale_codec::Decode::decode(input);
						match res {
							Err(_) => {
								return Err("Error decoding field RawEvent :: Rewarded.0".into())
							}
							Ok(a) => a,
						}
					})),
					x if x == 3usize as u8 => Ok(RawEvent::Slashed({
						let res = _parity_scale_codec::Decode::decode(input);
						match res {
							Err(_) => {
								return Err("Error decoding field RawEvent :: Slashed.0".into())
							}
							Ok(a) => a,
						}
					})),
					x => Err("No such variant in enum RawEvent".into()),
				}
			}
		}
	};
	impl<AccountId> core::fmt::Debug for RawEvent<AccountId>
	where
		AccountId: core::fmt::Debug,
	{
		fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
			match self {
				Self::SolutionStored(ref a0) => fmt
					.debug_tuple("RawEvent::SolutionStored")
					.field(a0)
					.finish(),
				Self::ElectionFinalized(ref a0) => fmt
					.debug_tuple("RawEvent::ElectionFinalized")
					.field(a0)
					.finish(),
				Self::Rewarded(ref a0) => fmt.debug_tuple("RawEvent::Rewarded").field(a0).finish(),
				Self::Slashed(ref a0) => fmt.debug_tuple("RawEvent::Slashed").field(a0).finish(),
				_ => Ok(()),
			}
		}
	}
	impl<AccountId> From<RawEvent<AccountId>> for () {
		fn from(_: RawEvent<AccountId>) -> () {
			()
		}
	}
	impl<AccountId> RawEvent<AccountId> {
		#[allow(dead_code)]
		#[doc(hidden)]
		pub fn metadata() -> &'static [::frame_support::event::EventMetadata] {
			&[
				::frame_support::event::EventMetadata {
					name: ::frame_support::event::DecodeDifferent::Encode("SolutionStored"),
					arguments: ::frame_support::event::DecodeDifferent::Encode(&[
						"ElectionCompute",
					]),
					documentation: ::frame_support::event::DecodeDifferent::Encode(&[
						r" A solution was sot",
					]),
				},
				::frame_support::event::EventMetadata {
					name: ::frame_support::event::DecodeDifferent::Encode("ElectionFinalized"),
					arguments: ::frame_support::event::DecodeDifferent::Encode(&[
						"Option<ElectionCompute>",
					]),
					documentation: ::frame_support::event::DecodeDifferent::Encode(&[]),
				},
				::frame_support::event::EventMetadata {
					name: ::frame_support::event::DecodeDifferent::Encode("Rewarded"),
					arguments: ::frame_support::event::DecodeDifferent::Encode(&["AccountId"]),
					documentation: ::frame_support::event::DecodeDifferent::Encode(&[]),
				},
				::frame_support::event::EventMetadata {
					name: ::frame_support::event::DecodeDifferent::Encode("Slashed"),
					arguments: ::frame_support::event::DecodeDifferent::Encode(&["AccountId"]),
					documentation: ::frame_support::event::DecodeDifferent::Encode(&[]),
				},
			]
		}
	}
	pub enum PalletError<T: Trait> {
		#[doc(hidden)]
		__Ignore(
			::frame_support::sp_std::marker::PhantomData<(T,)>,
			::frame_support::Never,
		),
		EarlySubmission,
		QueueFull,
		SubmissionQueuedFull,
		CannotPayDeposit,
	}
	impl<T: Trait> ::frame_support::sp_std::fmt::Debug for PalletError<T> {
		fn fmt(
			&self,
			f: &mut ::frame_support::sp_std::fmt::Formatter<'_>,
		) -> ::frame_support::sp_std::fmt::Result {
			f.write_str(self.as_str())
		}
	}
	impl<T: Trait> PalletError<T> {
		fn as_u8(&self) -> u8 {
			match self {
				PalletError::__Ignore(_, _) => {
					::std::rt::begin_panic_fmt(&::core::fmt::Arguments::new_v1(
						&["internal error: entered unreachable code: "],
						&match (&"`__Ignore` can never be constructed",) {
							(arg0,) => [::core::fmt::ArgumentV1::new(
								arg0,
								::core::fmt::Display::fmt,
							)],
						},
					))
				}
				PalletError::EarlySubmission => 0,
				PalletError::QueueFull => 0 + 1,
				PalletError::SubmissionQueuedFull => 0 + 1 + 1,
				PalletError::CannotPayDeposit => 0 + 1 + 1 + 1,
			}
		}
		fn as_str(&self) -> &'static str {
			match self {
				Self::__Ignore(_, _) => {
					::std::rt::begin_panic_fmt(&::core::fmt::Arguments::new_v1(
						&["internal error: entered unreachable code: "],
						&match (&"`__Ignore` can never be constructed",) {
							(arg0,) => [::core::fmt::ArgumentV1::new(
								arg0,
								::core::fmt::Display::fmt,
							)],
						},
					))
				}
				PalletError::EarlySubmission => "EarlySubmission",
				PalletError::QueueFull => "QueueFull",
				PalletError::SubmissionQueuedFull => "SubmissionQueuedFull",
				PalletError::CannotPayDeposit => "CannotPayDeposit",
			}
		}
	}
	impl<T: Trait> From<PalletError<T>> for &'static str {
		fn from(err: PalletError<T>) -> &'static str {
			err.as_str()
		}
	}
	impl<T: Trait> From<PalletError<T>> for ::frame_support::sp_runtime::DispatchError {
		fn from(err: PalletError<T>) -> Self {
			let index = <T::PalletInfo as ::frame_support::traits::PalletInfo>::index::<Module<T>>()
				.expect("Every active module has an index in the runtime; qed") as u8;
			::frame_support::sp_runtime::DispatchError::Module {
				index,
				error: err.as_u8(),
				message: Some(err.as_str()),
			}
		}
	}
	impl<T: Trait> ::frame_support::error::ModuleErrorMetadata for PalletError<T> {
		fn metadata() -> &'static [::frame_support::error::ErrorMetadata] {
			&[
				::frame_support::error::ErrorMetadata {
					name: ::frame_support::error::DecodeDifferent::Encode("EarlySubmission"),
					documentation: ::frame_support::error::DecodeDifferent::Encode(&[]),
				},
				::frame_support::error::ErrorMetadata {
					name: ::frame_support::error::DecodeDifferent::Encode("QueueFull"),
					documentation: ::frame_support::error::DecodeDifferent::Encode(&[]),
				},
				::frame_support::error::ErrorMetadata {
					name: ::frame_support::error::DecodeDifferent::Encode("SubmissionQueuedFull"),
					documentation: ::frame_support::error::DecodeDifferent::Encode(&[]),
				},
				::frame_support::error::ErrorMetadata {
					name: ::frame_support::error::DecodeDifferent::Encode("CannotPayDeposit"),
					documentation: ::frame_support::error::DecodeDifferent::Encode(&[]),
				},
			]
		}
	}
	pub struct Module<T: Trait>(::frame_support::sp_std::marker::PhantomData<(T,)>);
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<T: ::core::clone::Clone + Trait> ::core::clone::Clone for Module<T> {
		#[inline]
		fn clone(&self) -> Module<T> {
			match *self {
				Module(ref __self_0_0) => Module(::core::clone::Clone::clone(&(*__self_0_0))),
			}
		}
	}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<T: ::core::marker::Copy + Trait> ::core::marker::Copy for Module<T> {}
	impl<T: Trait> ::core::marker::StructuralPartialEq for Module<T> {}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<T: ::core::cmp::PartialEq + Trait> ::core::cmp::PartialEq for Module<T> {
		#[inline]
		fn eq(&self, other: &Module<T>) -> bool {
			match *other {
				Module(ref __self_1_0) => match *self {
					Module(ref __self_0_0) => (*__self_0_0) == (*__self_1_0),
				},
			}
		}
		#[inline]
		fn ne(&self, other: &Module<T>) -> bool {
			match *other {
				Module(ref __self_1_0) => match *self {
					Module(ref __self_0_0) => (*__self_0_0) != (*__self_1_0),
				},
			}
		}
	}
	impl<T: Trait> ::core::marker::StructuralEq for Module<T> {}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<T: ::core::cmp::Eq + Trait> ::core::cmp::Eq for Module<T> {
		#[inline]
		#[doc(hidden)]
		fn assert_receiver_is_total_eq(&self) -> () {
			{
				let _: ::core::cmp::AssertParamIsEq<
					::frame_support::sp_std::marker::PhantomData<(T,)>,
				>;
			}
		}
	}
	impl<T: Trait> core::fmt::Debug for Module<T>
	where
		T: core::fmt::Debug,
	{
		fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
			fmt.debug_tuple("Module").field(&self.0).finish()
		}
	}
	impl<T: frame_system::Trait + Trait>
		::frame_support::traits::OnInitialize<<T as frame_system::Trait>::BlockNumber> for Module<T>
	{
		fn on_initialize(now: T::BlockNumber) -> Weight {
			let __within_span__ = {
				if ::tracing::Level::TRACE <= ::tracing::level_filters::STATIC_MAX_LEVEL
					&& ::tracing::Level::TRACE <= ::tracing::level_filters::LevelFilter::current()
				{
					use ::tracing::__macro_support::*;
					let callsite = {
						use ::tracing::__macro_support::MacroCallsite;
						static META: ::tracing::Metadata<'static> = {
							::tracing_core::metadata::Metadata::new(
								"on_initialize",
								"frame_election_providers::two_phase",
								::tracing::Level::TRACE,
								Some("frame/election-providers/src/two_phase/mod.rs"),
								Some(250u32),
								Some("frame_election_providers::two_phase"),
								::tracing_core::field::FieldSet::new(
									&[],
									::tracing_core::callsite::Identifier(&CALLSITE),
								),
								::tracing::metadata::Kind::SPAN,
							)
						};
						static CALLSITE: MacroCallsite = MacroCallsite::new(&META);
						CALLSITE.register();
						&CALLSITE
					};
					if callsite.is_enabled() {
						let meta = callsite.metadata();
						::tracing::Span::new(meta, &{ meta.fields().value_set(&[]) })
					} else {
						::tracing::Span::none()
					}
				} else {
					::tracing::Span::none()
				}
			};
			let __tracing_guard__ = __within_span__.enter();
			{
				let next_election = T::ElectionDataProvider::next_election_prediction(now);
				let next_election = next_election.max(now);
				let signed_deadline = T::SignedPhase::get() + T::UnsignedPhase::get();
				let unsigned_deadline = T::UnsignedPhase::get();
				let remaining = next_election - now;
				match Self::current_phase() {
					Phase::Off if remaining <= signed_deadline && remaining > unsigned_deadline => {
						CurrentPhase::put(Phase::Signed);
						Self::start_signed_phase();
					}
					Phase::Signed if remaining <= unsigned_deadline && remaining > 0.into() => {
						let found_solution = Self::finalize_signed_phase();
						CurrentPhase::put(Phase::Unsigned(!found_solution));
					}
					_ => {}
				}
				Default::default()
			}
		}
	}
	impl<T: Trait> ::frame_support::traits::OnRuntimeUpgrade for Module<T> {}
	impl<T: frame_system::Trait + Trait>
		::frame_support::traits::OnFinalize<<T as frame_system::Trait>::BlockNumber> for Module<T>
	{
	}
	impl<T: frame_system::Trait + Trait>
		::frame_support::traits::OffchainWorker<<T as frame_system::Trait>::BlockNumber> for Module<T>
	{
		fn offchain_worker(n: T::BlockNumber) {}
	}
	impl<T: Trait> Module<T> {
		/// Deposits an event using `frame_system::Module::deposit_event`.
		fn deposit_event(event: impl Into<<T as Trait>::Event>) {
			<frame_system::Module<T>>::deposit_event(event.into())
		}
	}
	#[cfg(feature = "std")]
	impl<T: Trait> ::frame_support::traits::IntegrityTest for Module<T> {}
	/// Can also be called using [`Call`].
	///
	/// [`Call`]: enum.Call.html
	impl<T: Trait> Module<T> {
		///
		/// NOTE: Calling this function will bypass origin filters.
		fn submit(origin: T::Origin, solution: RawSolution) -> DispatchResultWithPostInfo {
			let __within_span__ = {
				if ::tracing::Level::TRACE <= ::tracing::level_filters::STATIC_MAX_LEVEL
					&& ::tracing::Level::TRACE <= ::tracing::level_filters::LevelFilter::current()
				{
					use ::tracing::__macro_support::*;
					let callsite = {
						use ::tracing::__macro_support::MacroCallsite;
						static META: ::tracing::Metadata<'static> = {
							::tracing_core::metadata::Metadata::new(
								"submit",
								"frame_election_providers::two_phase",
								::tracing::Level::TRACE,
								Some("frame/election-providers/src/two_phase/mod.rs"),
								Some(250u32),
								Some("frame_election_providers::two_phase"),
								::tracing_core::field::FieldSet::new(
									&[],
									::tracing_core::callsite::Identifier(&CALLSITE),
								),
								::tracing::metadata::Kind::SPAN,
							)
						};
						static CALLSITE: MacroCallsite = MacroCallsite::new(&META);
						CALLSITE.register();
						&CALLSITE
					};
					if callsite.is_enabled() {
						let meta = callsite.metadata();
						::tracing::Span::new(meta, &{ meta.fields().value_set(&[]) })
					} else {
						::tracing::Span::none()
					}
				} else {
					::tracing::Span::none()
				}
			};
			let __tracing_guard__ = __within_span__.enter();
			let who = ensure_signed(origin)?;
			{
				if !Self::current_phase().is_signed() {
					{
						return Err(PalletError::<T>::EarlySubmission.into());
					};
				}
			};
			let queue_size = <SignedSubmissions<T>>::decode_len().unwrap_or_default() as u32;
			{
				if !(queue_size <= T::MaxSignedSubmissions::get()) {
					{
						return Err(PalletError::<T>::SubmissionQueuedFull.into());
					};
				}
			};
			let mut signed_submissions = Self::signed_submissions();
			let maybe_index = Self::insert_submission(&who, &mut signed_submissions, solution);
			{
				if !maybe_index.is_some() {
					{
						return Err(PalletError::<T>::QueueFull.into());
					};
				}
			};
			let index = maybe_index.expect("Option checked to be `Some`; qed.");
			let deposit = signed_submissions[index].deposit;
			T::Currency::reserve(&who, deposit).map_err(|_| PalletError::<T>::CannotPayDeposit)?;
			if true {
				if !(signed_submissions.len() as u32 == queue_size + 1
					|| signed_submissions.len() as u32 == T::MaxSignedSubmissions::get())
				{
					{
						:: std :: rt :: begin_panic ( "assertion failed: signed_submissions.len() as u32 == queue_size + 1 ||\n    signed_submissions.len() as u32 == T::MaxSignedSubmissions::get()" )
					}
				};
			};
			<SignedSubmissions<T>>::put(signed_submissions);
			Self::deposit_event(RawEvent::SolutionStored(ElectionCompute::Signed));
			Ok(None.into())
		}
		#[allow(unreachable_code)]
		///
		/// NOTE: Calling this function will bypass origin filters.
		fn submit_unsigned(
			origin: T::Origin,
			solution: RawSolution,
		) -> ::frame_support::dispatch::DispatchResult {
			let __within_span__ = {
				if ::tracing::Level::TRACE <= ::tracing::level_filters::STATIC_MAX_LEVEL
					&& ::tracing::Level::TRACE <= ::tracing::level_filters::LevelFilter::current()
				{
					use ::tracing::__macro_support::*;
					let callsite = {
						use ::tracing::__macro_support::MacroCallsite;
						static META: ::tracing::Metadata<'static> = {
							::tracing_core::metadata::Metadata::new(
								"submit_unsigned",
								"frame_election_providers::two_phase",
								::tracing::Level::TRACE,
								Some("frame/election-providers/src/two_phase/mod.rs"),
								Some(250u32),
								Some("frame_election_providers::two_phase"),
								::tracing_core::field::FieldSet::new(
									&[],
									::tracing_core::callsite::Identifier(&CALLSITE),
								),
								::tracing::metadata::Kind::SPAN,
							)
						};
						static CALLSITE: MacroCallsite = MacroCallsite::new(&META);
						CALLSITE.register();
						&CALLSITE
					};
					if callsite.is_enabled() {
						let meta = callsite.metadata();
						::tracing::Span::new(meta, &{ meta.fields().value_set(&[]) })
					} else {
						::tracing::Span::none()
					}
				} else {
					::tracing::Span::none()
				}
			};
			let __tracing_guard__ = __within_span__.enter();
			{
				ensure_none(origin)?;
				Self::deposit_event(RawEvent::SolutionStored(ElectionCompute::Unsigned));
				{
					::std::rt::begin_panic("not implemented")
				}
			}
			Ok(())
		}
	}
	/// Dispatchable calls.
	///
	/// Each variant of this enum maps to a dispatchable function from the associated module.
	pub enum Call<T: Trait> {
		#[doc(hidden)]
		#[codec(skip)]
		__PhantomItem(
			::frame_support::sp_std::marker::PhantomData<(T,)>,
			::frame_support::Never,
		),
		#[allow(non_camel_case_types)]
		submit(RawSolution),
		#[allow(non_camel_case_types)]
		submit_unsigned(RawSolution),
	}
	const _: () = {
		#[allow(unknown_lints)]
		#[allow(rust_2018_idioms)]
		extern crate codec as _parity_scale_codec;
		impl<T: Trait> _parity_scale_codec::Encode for Call<T> {
			fn encode_to<EncOut: _parity_scale_codec::Output>(&self, dest: &mut EncOut) {
				match *self {
					Call::submit(ref aa) => {
						dest.push_byte(0usize as u8);
						dest.push(aa);
					}
					Call::submit_unsigned(ref aa) => {
						dest.push_byte(1usize as u8);
						dest.push(aa);
					}
					_ => (),
				}
			}
		}
		impl<T: Trait> _parity_scale_codec::EncodeLike for Call<T> {}
	};
	const _: () = {
		#[allow(unknown_lints)]
		#[allow(rust_2018_idioms)]
		extern crate codec as _parity_scale_codec;
		impl<T: Trait> _parity_scale_codec::Decode for Call<T> {
			fn decode<DecIn: _parity_scale_codec::Input>(
				input: &mut DecIn,
			) -> core::result::Result<Self, _parity_scale_codec::Error> {
				match input.read_byte()? {
					x if x == 0usize as u8 => Ok(Call::submit({
						let res = _parity_scale_codec::Decode::decode(input);
						match res {
							Err(_) => return Err("Error decoding field Call :: submit.0".into()),
							Ok(a) => a,
						}
					})),
					x if x == 1usize as u8 => Ok(Call::submit_unsigned({
						let res = _parity_scale_codec::Decode::decode(input);
						match res {
							Err(_) => {
								return Err("Error decoding field Call :: submit_unsigned.0".into())
							}
							Ok(a) => a,
						}
					})),
					x => Err("No such variant in enum Call".into()),
				}
			}
		}
	};
	impl<T: Trait> ::frame_support::dispatch::GetDispatchInfo for Call<T> {
		fn get_dispatch_info(&self) -> ::frame_support::dispatch::DispatchInfo {
			match *self {
				Call::submit(ref solution) => {
					let base_weight = 0;
					let weight =
						<dyn ::frame_support::dispatch::WeighData<(&RawSolution,)>>::weigh_data(
							&base_weight,
							(solution,),
						);
					let class = < dyn :: frame_support :: dispatch :: ClassifyDispatch < ( & RawSolution , ) > > :: classify_dispatch ( & base_weight , ( solution , ) ) ;
					let pays_fee =
						<dyn ::frame_support::dispatch::PaysFee<(&RawSolution,)>>::pays_fee(
							&base_weight,
							(solution,),
						);
					::frame_support::dispatch::DispatchInfo {
						weight,
						class,
						pays_fee,
					}
				}
				Call::submit_unsigned(ref solution) => {
					let base_weight = 0;
					let weight =
						<dyn ::frame_support::dispatch::WeighData<(&RawSolution,)>>::weigh_data(
							&base_weight,
							(solution,),
						);
					let class = < dyn :: frame_support :: dispatch :: ClassifyDispatch < ( & RawSolution , ) > > :: classify_dispatch ( & base_weight , ( solution , ) ) ;
					let pays_fee =
						<dyn ::frame_support::dispatch::PaysFee<(&RawSolution,)>>::pays_fee(
							&base_weight,
							(solution,),
						);
					::frame_support::dispatch::DispatchInfo {
						weight,
						class,
						pays_fee,
					}
				}
				Call::__PhantomItem(_, _) => {
					::std::rt::begin_panic_fmt(&::core::fmt::Arguments::new_v1(
						&["internal error: entered unreachable code: "],
						&match (&"__PhantomItem should never be used.",) {
							(arg0,) => [::core::fmt::ArgumentV1::new(
								arg0,
								::core::fmt::Display::fmt,
							)],
						},
					))
				}
			}
		}
	}
	impl<T: Trait> ::frame_support::dispatch::GetCallName for Call<T> {
		fn get_call_name(&self) -> &'static str {
			match *self {
				Call::submit(ref solution) => {
					let _ = (solution);
					"submit"
				}
				Call::submit_unsigned(ref solution) => {
					let _ = (solution);
					"submit_unsigned"
				}
				Call::__PhantomItem(_, _) => {
					::std::rt::begin_panic_fmt(&::core::fmt::Arguments::new_v1(
						&["internal error: entered unreachable code: "],
						&match (&"__PhantomItem should never be used.",) {
							(arg0,) => [::core::fmt::ArgumentV1::new(
								arg0,
								::core::fmt::Display::fmt,
							)],
						},
					))
				}
			}
		}
		fn get_call_names() -> &'static [&'static str] {
			&["submit", "submit_unsigned"]
		}
	}
	impl<T: Trait> ::frame_support::dispatch::Clone for Call<T> {
		fn clone(&self) -> Self {
			match *self {
				Call::submit(ref solution) => Call::submit((*solution).clone()),
				Call::submit_unsigned(ref solution) => Call::submit_unsigned((*solution).clone()),
				_ => ::std::rt::begin_panic("internal error: entered unreachable code"),
			}
		}
	}
	impl<T: Trait> ::frame_support::dispatch::PartialEq for Call<T> {
		fn eq(&self, _other: &Self) -> bool {
			match *self {
				Call::submit(ref solution) => {
					let self_params = (solution,);
					if let Call::submit(ref solution) = *_other {
						self_params == (solution,)
					} else {
						match *_other {
							Call::__PhantomItem(_, _) => {
								::std::rt::begin_panic("internal error: entered unreachable code")
							}
							_ => false,
						}
					}
				}
				Call::submit_unsigned(ref solution) => {
					let self_params = (solution,);
					if let Call::submit_unsigned(ref solution) = *_other {
						self_params == (solution,)
					} else {
						match *_other {
							Call::__PhantomItem(_, _) => {
								::std::rt::begin_panic("internal error: entered unreachable code")
							}
							_ => false,
						}
					}
				}
				_ => ::std::rt::begin_panic("internal error: entered unreachable code"),
			}
		}
	}
	impl<T: Trait> ::frame_support::dispatch::Eq for Call<T> {}
	impl<T: Trait> ::frame_support::dispatch::fmt::Debug for Call<T> {
		fn fmt(
			&self,
			_f: &mut ::frame_support::dispatch::fmt::Formatter,
		) -> ::frame_support::dispatch::result::Result<(), ::frame_support::dispatch::fmt::Error> {
			match *self {
				Call::submit(ref solution) => _f.write_fmt(::core::fmt::Arguments::new_v1(
					&["", ""],
					&match (&"submit", &(solution.clone(),)) {
						(arg0, arg1) => [
							::core::fmt::ArgumentV1::new(arg0, ::core::fmt::Display::fmt),
							::core::fmt::ArgumentV1::new(arg1, ::core::fmt::Debug::fmt),
						],
					},
				)),
				Call::submit_unsigned(ref solution) => {
					_f.write_fmt(::core::fmt::Arguments::new_v1(
						&["", ""],
						&match (&"submit_unsigned", &(solution.clone(),)) {
							(arg0, arg1) => [
								::core::fmt::ArgumentV1::new(arg0, ::core::fmt::Display::fmt),
								::core::fmt::ArgumentV1::new(arg1, ::core::fmt::Debug::fmt),
							],
						},
					))
				}
				_ => ::std::rt::begin_panic("internal error: entered unreachable code"),
			}
		}
	}
	impl<T: Trait> ::frame_support::traits::UnfilteredDispatchable for Call<T> {
		type Origin = T::Origin;
		fn dispatch_bypass_filter(
			self,
			_origin: Self::Origin,
		) -> ::frame_support::dispatch::DispatchResultWithPostInfo {
			match self {
				Call::submit(solution) => <Module<T>>::submit(_origin, solution)
					.map(Into::into)
					.map_err(Into::into),
				Call::submit_unsigned(solution) => <Module<T>>::submit_unsigned(_origin, solution)
					.map(Into::into)
					.map_err(Into::into),
				Call::__PhantomItem(_, _) => {
					::std::rt::begin_panic_fmt(&::core::fmt::Arguments::new_v1(
						&["internal error: entered unreachable code: "],
						&match (&"__PhantomItem should never be used.",) {
							(arg0,) => [::core::fmt::ArgumentV1::new(
								arg0,
								::core::fmt::Display::fmt,
							)],
						},
					))
				}
			}
		}
	}
	impl<T: Trait> ::frame_support::dispatch::Callable<T> for Module<T> {
		type Call = Call<T>;
	}
	impl<T: Trait> Module<T> {
		#[doc(hidden)]
		#[allow(dead_code)]
		pub fn call_functions() -> &'static [::frame_support::dispatch::FunctionMetadata] {
			&[
				::frame_support::dispatch::FunctionMetadata {
					name: ::frame_support::dispatch::DecodeDifferent::Encode("submit"),
					arguments: ::frame_support::dispatch::DecodeDifferent::Encode(&[
						::frame_support::dispatch::FunctionArgumentMetadata {
							name: ::frame_support::dispatch::DecodeDifferent::Encode("solution"),
							ty: ::frame_support::dispatch::DecodeDifferent::Encode("RawSolution"),
						},
					]),
					documentation: ::frame_support::dispatch::DecodeDifferent::Encode(&[]),
				},
				::frame_support::dispatch::FunctionMetadata {
					name: ::frame_support::dispatch::DecodeDifferent::Encode("submit_unsigned"),
					arguments: ::frame_support::dispatch::DecodeDifferent::Encode(&[
						::frame_support::dispatch::FunctionArgumentMetadata {
							name: ::frame_support::dispatch::DecodeDifferent::Encode("solution"),
							ty: ::frame_support::dispatch::DecodeDifferent::Encode("RawSolution"),
						},
					]),
					documentation: ::frame_support::dispatch::DecodeDifferent::Encode(&[]),
				},
			]
		}
	}
	impl<T: 'static + Trait> Module<T> {
		#[doc(hidden)]
		#[allow(dead_code)]
		pub fn module_constants_metadata(
		) -> &'static [::frame_support::dispatch::ModuleConstantMetadata] {
			&[]
		}
	}
	impl<T: Trait> ::frame_support::dispatch::ModuleErrorMetadata for Module<T> {
		fn metadata() -> &'static [::frame_support::dispatch::ErrorMetadata] {
			<&'static str as ::frame_support::dispatch::ModuleErrorMetadata>::metadata()
		}
	}
	pub enum FeasibilityError {
		/// Wrong number of winners presented.
		WrongWinnerCount,
		/// The snapshot is not available.
		///
		/// This must be an internal error of the chain.
		SnapshotUnavailable,
		/// Internal error from the election crate.
		NposElectionError(sp_npos_elections::Error),
		/// A vote is invalid.
		InvalidVote,
		/// A voter is invalid.
		InvalidVoter,
		/// A winner is invalid.
		InvalidWinner,
		/// The given score was invalid.
		InvalidScore,
	}
	impl From<sp_npos_elections::Error> for FeasibilityError {
		fn from(e: sp_npos_elections::Error) -> Self {
			FeasibilityError::NposElectionError(e)
		}
	}
	impl<T: Trait> Module<T> {
		/// Checks the feasibility of a solution.
		fn feasibility_check(
			solution: RawSolution,
			compute: ElectionCompute,
		) -> Result<ReadySolution<T::AccountId>, FeasibilityError> {
			let RawSolution {
				winners,
				compact,
				score,
			} = solution;
			{
				if !(compact.unique_targets().len() == winners.len()) {
					{
						return Err(FeasibilityError::WrongWinnerCount.into());
					};
				}
			};
			{
				if !(winners.len() as u32 == Self::desired_targets()) {
					{
						return Err(FeasibilityError::WrongWinnerCount.into());
					};
				}
			};
			let snapshot_voters =
				Self::snapshot_voters().ok_or(FeasibilityError::SnapshotUnavailable)?;
			let snapshot_targets =
				Self::snapshot_targets().ok_or(FeasibilityError::SnapshotUnavailable)?;
			let voter_at = |i: VoterIndex| -> Option<T::AccountId> {
				snapshot_voters.get(i as usize).map(|(x, _, _)| x).cloned()
			};
			let target_at = |i: TargetIndex| -> Option<T::AccountId> {
				snapshot_targets.get(i as usize).cloned()
			};
			let winners = winners
				.into_iter()
				.map(|i| target_at(i).ok_or(FeasibilityError::InvalidWinner))
				.collect::<Result<Vec<T::AccountId>, FeasibilityError>>()?;
			let assignments = compact
				.into_assignment(voter_at, target_at)
				.map_err::<FeasibilityError, _>(Into::into)?;
			let _ = assignments
				.iter()
				.map(|Assignment { who, distribution }| {
					snapshot_voters.iter().find(|(v, _, _)| v == who).map_or(
						Err(FeasibilityError::InvalidVoter),
						|(_, _, t)| {
							if distribution.iter().map(|(x, _)| x).all(|x| t.contains(x))
								&& T::ElectionDataProvider::feasibility_check_assignment::<
									OffchainAccuracy,
								>(who, distribution)
							{
								Ok(())
							} else {
								Err(FeasibilityError::InvalidVote)
							}
						},
					)
				})
				.collect::<Result<(), FeasibilityError>>()?;
			let stake_of = |who: &T::AccountId| -> crate::VoteWeight {
				snapshot_voters
					.iter()
					.find(|(x, _, _)| x == who)
					.map(|(_, x, _)| *x)
					.unwrap_or_default()
			};
			use sp_npos_elections::{assignment_ratio_to_staked_normalized, build_support_map};
			let staked_assignments = assignment_ratio_to_staked_normalized(assignments, stake_of)
				.map_err::<FeasibilityError, _>(Into::into)?;
			let supports = build_support_map(&winners, &staked_assignments)
				.map_err::<FeasibilityError, _>(Into::into)?;
			let known_score = evaluate_support(&supports);
			{
				if !(known_score == score) {
					{
						return Err(FeasibilityError::InvalidScore.into());
					};
				}
			};
			let supports = supports.flatten();
			Ok(ReadySolution {
				winners,
				supports,
				compute,
			})
		}
		fn onchain_fallback() -> Result<FlatSupportMap<T::AccountId>, crate::Error> {
			let desired_targets = Self::desired_targets() as usize;
			let voters = Self::snapshot_voters().ok_or(crate::Error::SnapshotUnAvailable)?;
			let targets = Self::snapshot_targets().ok_or(crate::Error::SnapshotUnAvailable)?;
			<OnChainSequentialPhragmen as ElectionProvider<T::AccountId>>::elect::<ChainAccuracy>(
				desired_targets,
				targets,
				voters,
			)
		}
	}
	impl<T: Trait> crate::ElectionProvider<T::AccountId> for Module<T> {
		fn elect<P: PerThing>(
			_to_elect: usize,
			_targets: Vec<T::AccountId>,
			_voters: Vec<(T::AccountId, VoteWeight, Vec<T::AccountId>)>,
		) -> Result<FlatSupportMap<T::AccountId>, crate::Error>
		where
			ExtendedBalance: From<<P as PerThing>::Inner>,
			P: sp_std::ops::Mul<ExtendedBalance, Output = ExtendedBalance>,
		{
			Self::queued_solution()
				.map_or_else(
					|| Self::onchain_fallback().map(|r| (r, ElectionCompute::OnChain)),
					|ReadySolution {
					     supports, compute, ..
					 }| Ok((supports, compute)),
				)
				.map(|(supports, compute)| {
					CurrentPhase::put(Phase::Off);
					<SnapshotVoters<T>>::kill();
					<SnapshotTargets<T>>::kill();
					Self::deposit_event(RawEvent::ElectionFinalized(Some(compute)));
					supports
				})
				.map_err(|err| {
					Self::deposit_event(RawEvent::ElectionFinalized(None));
					err
				})
		}
		fn ongoing() -> bool {
			match Self::current_phase() {
				Phase::Signed | Phase::Unsigned(_) => true,
				_ => false,
			}
		}
	}
}
use sp_arithmetic::PerThing;
#[doc(hidden)]
pub use sp_npos_elections::VoteWeight;
use sp_npos_elections::{ExtendedBalance, FlatSupportMap};
use sp_runtime::RuntimeDebug;
#[doc(hidden)]
pub use sp_std::convert::TryInto;
/// A bridge between the entity requesting a long-lasting election from something that implements
/// [`ElectionProvider`], such as the [`two_phase`] module.
pub trait ElectionDataProvider<AccountId, B> {
	fn targets() -> Vec<AccountId>;
	fn voters() -> Vec<(AccountId, VoteWeight, Vec<AccountId>)>;
	fn desired_targets() -> u32;
	fn feasibility_check_assignment<P: PerThing>(
		who: &AccountId,
		distribution: &[(AccountId, P)],
	) -> bool;
	fn next_election_prediction(now: B) -> B;
}
#[cfg(feature = "std")]
impl<AccountId, B: Default> ElectionDataProvider<AccountId, B> for () {
	fn targets() -> Vec<AccountId> {
		Default::default()
	}
	fn voters() -> Vec<(AccountId, VoteWeight, Vec<AccountId>)> {
		Default::default()
	}
	fn desired_targets() -> u32 {
		Default::default()
	}
	fn feasibility_check_assignment<P: PerThing>(_: &AccountId, _: &[(AccountId, P)]) -> bool {
		Default::default()
	}
	fn next_election_prediction(_: B) -> B {
		Default::default()
	}
}
/// Something that can compute the result of an election and pass it back to a pallet.
pub trait ElectionProvider<AccountId> {
	/// Elect a new set of winners.
	///
	/// The result is returned in a target major format, namely as a support map.
	fn elect<P: PerThing>(
		to_elect: usize,
		targets: Vec<AccountId>,
		voters: Vec<(AccountId, VoteWeight, Vec<AccountId>)>,
	) -> Result<FlatSupportMap<AccountId>, Error>
	where
		ExtendedBalance: From<<P as PerThing>::Inner>,
		P: sp_std::ops::Mul<ExtendedBalance, Output = ExtendedBalance>;
	/// Returns true if an election is still ongoing.
	fn ongoing() -> bool;
}
pub enum Error {
	ElectionFailed,
	SnapshotUnAvailable,
	Internal(sp_npos_elections::Error),
}
impl core::fmt::Debug for Error {
	fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
		match self {
			Self::ElectionFailed => fmt.debug_tuple("Error::ElectionFailed").finish(),
			Self::SnapshotUnAvailable => fmt.debug_tuple("Error::SnapshotUnAvailable").finish(),
			Self::Internal(ref a0) => fmt.debug_tuple("Error::Internal").field(a0).finish(),
			_ => Ok(()),
		}
	}
}
impl ::core::marker::StructuralEq for Error {}
#[automatically_derived]
#[allow(unused_qualifications)]
impl ::core::cmp::Eq for Error {
	#[inline]
	#[doc(hidden)]
	fn assert_receiver_is_total_eq(&self) -> () {
		{
			let _: ::core::cmp::AssertParamIsEq<sp_npos_elections::Error>;
		}
	}
}
impl ::core::marker::StructuralPartialEq for Error {}
#[automatically_derived]
#[allow(unused_qualifications)]
impl ::core::cmp::PartialEq for Error {
	#[inline]
	fn eq(&self, other: &Error) -> bool {
		{
			let __self_vi = unsafe { ::core::intrinsics::discriminant_value(&*self) };
			let __arg_1_vi = unsafe { ::core::intrinsics::discriminant_value(&*other) };
			if true && __self_vi == __arg_1_vi {
				match (&*self, &*other) {
					(&Error::Internal(ref __self_0), &Error::Internal(ref __arg_1_0)) => {
						(*__self_0) == (*__arg_1_0)
					}
					_ => true,
				}
			} else {
				false
			}
		}
	}
	#[inline]
	fn ne(&self, other: &Error) -> bool {
		{
			let __self_vi = unsafe { ::core::intrinsics::discriminant_value(&*self) };
			let __arg_1_vi = unsafe { ::core::intrinsics::discriminant_value(&*other) };
			if true && __self_vi == __arg_1_vi {
				match (&*self, &*other) {
					(&Error::Internal(ref __self_0), &Error::Internal(ref __arg_1_0)) => {
						(*__self_0) != (*__arg_1_0)
					}
					_ => false,
				}
			} else {
				true
			}
		}
	}
}
impl From<sp_npos_elections::Error> for Error {
	fn from(err: sp_npos_elections::Error) -> Self {
		Error::Internal(err)
	}
}
