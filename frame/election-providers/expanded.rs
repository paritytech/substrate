#![feature(prelude_import)]
//! Reusable Election Providers.
//!
//! The core functionality of this crate is around [`ElectionProvider`]. An election provider is a
//! struct, module, or anything else that implements [`ElectionProvider`]. Such types can then be
//! passed around to other crates and pallets that need election functionality.
//!
//! Two main election providers are implemented in this crate.
//!
//! 1.  [`onchain`]: A `struct` that perform the election onchain (i.e. in the fly). This type is
//!     likely to be expensive for most chains and damage the block time. Only use when you are sure
//!     that the inputs are bounded and small enough.
//! 2. [`two_phase`]: An individual `pallet` that performs the election in two phases, signed and
//!    unsigned. Needless to say, the pallet needs to be included in the final runtime.
#[prelude_import]
use std::prelude::v1::*;
#[macro_use]
extern crate std;
use sp_std::{fmt::Debug, prelude::*};
/// The onchain module.
pub mod onchain {
	use crate::{ElectionProvider, FlattenSupportMap, Supports};
	use sp_arithmetic::PerThing;
	use sp_npos_elections::{
		ElectionResult, ExtendedBalance, IdentifierT, PerThing128, VoteWeight,
	};
	use sp_runtime::RuntimeDebug;
	use sp_std::{collections::btree_map::BTreeMap, prelude::*};
	/// Errors of the on-chain election.
	pub enum Error {
		/// An internal error in the NPoS elections crate.
		NposElections(sp_npos_elections::Error),
	}
	impl core::fmt::Debug for Error {
		fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
			match self {
				Self::NposElections(ref a0) => {
					fmt.debug_tuple("Error::NposElections").field(a0).finish()
				}
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
			match (&*self, &*other) {
				(&Error::NposElections(ref __self_0), &Error::NposElections(ref __arg_1_0)) => {
					(*__self_0) == (*__arg_1_0)
				}
			}
		}
		#[inline]
		fn ne(&self, other: &Error) -> bool {
			match (&*self, &*other) {
				(&Error::NposElections(ref __self_0), &Error::NposElections(ref __arg_1_0)) => {
					(*__self_0) != (*__arg_1_0)
				}
			}
		}
	}
	impl From<sp_npos_elections::Error> for Error {
		fn from(e: sp_npos_elections::Error) -> Self {
			Error::NposElections(e)
		}
	}
	pub struct OnChainSequentialPhragmen;
	impl<AccountId: IdentifierT> ElectionProvider<AccountId> for OnChainSequentialPhragmen {
		type Error = Error;
		const NEEDS_ELECT_DATA: bool = true;
		fn elect<P: PerThing128>(
			to_elect: usize,
			targets: Vec<AccountId>,
			voters: Vec<(AccountId, VoteWeight, Vec<AccountId>)>,
		) -> Result<Supports<AccountId>, Self::Error>
		where
			ExtendedBalance: From<<P as PerThing>::Inner>,
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
/// The two-phase module.
pub mod two_phase {
	//! # Two phase election provider pallet.
	//!
	//! As the name suggests, this election provider has two distinct phases (see [`Phase`]), signed and
	//! unsigned.
	//!
	//! ## Phases
	//!
	//! The timeline of pallet is as follows. At each block,
	//! [`ElectionDataProvider::next_election_prediction`] is used to estimate the time remaining to the
	//! next call to `elect`. Based on this, a phase is chosen. The timeline is as follows.
	//!
	//! ```ignore
	//!                                                                    elect()
	//!                 +   <--T::SignedPhase-->  +  <--T::UnsignedPhase-->   +
	//!   +-------------------------------------------------------------------+
	//!    Phase::Off   +       Phase::Signed     +      Phase::Unsigned      +
	//!
	//! Note that the unsigned phase starts `T::UnsignedPhase` blocks before the
	//! `next_election_prediction`, but only ends when a call to `ElectionProvider::elect` happens.
	//!
	//! ```
	//! ### Signed Phase
	//!
	//!	In the signed phase, solutions (of type [`RawSolution`]) are submitted and queued on chain. A
	//! deposit is reserved, based on the size of the solution, for the cost of keeping this solution
	//! on-chain for a number of blocks. A maximum of [`Trait::MaxSignedSubmissions`] solutions are
	//! stored. The queue is always sorted based on score (worse -> best).
	//!
	//! Upon arrival of a new solution:
	//!
	//! 1. If the queue is not full, it is stored.
	//! 2. If the queue is full but the submitted solution is better than one of the queued ones, the
	//!    worse solution is discarded (TODO: what to do with the bond?) and the new solution is stored
	//!    in the correct index.
	//! 3. If the queue is full and the solution is not an improvement compared to any of the queued
	//!    ones, it is instantly rejected and no additional bond is reserved.
	//!
	//! A signed solution cannot be reversed, taken back, updated, or retracted. In other words, the
	//! origin can not bail out in any way.
	//!
	//! Upon the end of the signed phase, the solutions are examined from worse to best (i.e. `pop()`ed
	//! until drained). Each solution undergoes an expensive [`Module::feasibility_check`], which ensure
	//! the score claimed by this score was correct, among other checks. At each step, if the current
	//! best solution is passes the feasibility check, it is considered to be the best one. The sender
	//! of the origin is rewarded, and the rest of the queued solutions get their deposit back, without
	//! being checked.
	//!
	//! The following example covers all of the cases at the end of the signed phase:
	//!
	//! ```ignore
	//! Queue
	//! +-------------------------------+
	//! |Solution(score=20, valid=false)| +-->  Slashed
	//! +-------------------------------+
	//! |Solution(score=15, valid=true )| +-->  Rewarded
	//! +-------------------------------+
	//! |Solution(score=10, valid=true )| +-->  Discarded
	//! +-------------------------------+
	//! |Solution(score=05, valid=false)| +-->  Discarded
	//! +-------------------------------+
	//! |             None              |
	//! +-------------------------------+
	//! ```
	//!
	//! Note that both of the bottom solutions end up being discarded and get their deposit back,
	//! despite one of them being invalid.
	//!
	//! ## Unsigned Phase
	//!
	//! If signed phase ends with a good solution, then the unsigned phase will be `active`
	//! ([`Phase::Unsigned(true)`]), else the unsigned phase will be `passive`.
	//!
	//! TODO
	//!
	//! ### Fallback
	//!
	//! If we reach the end of both phases (i.e. call to `ElectionProvider::elect` happens) and no good
	//! solution is queued, then we fallback to an on-chain election. The on-chain election is slow, and
	//! contains to balancing or reduction post-processing.
	//!
	//! ## Correct Submission
	//!
	//! TODO
	//!
	//! ## Accuracy
	//!
	//! TODO
	//!
	use crate::{
		onchain::OnChainSequentialPhragmen, ElectionDataProvider, ElectionProvider,
		FlattenSupportMap, Supports,
	};
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
		assignment_ratio_to_staked_normalized, build_support_map, evaluate_support, Assignment,
		CompactSolution, ElectionScore, ExtendedBalance, PerThing128, VoteWeight,
	};
	use sp_runtime::{traits::Zero, InnerOf, PerThing, Perbill, RuntimeDebug};
	use sp_std::prelude::*;
	#[macro_use]
	pub(crate) mod macros {
		//! Some helper macros for this crate.
	}
	pub mod signed {
		//! The signed phase implementation.
		use crate::two_phase::*;
		use codec::Encode;
		use sp_arithmetic::traits::SaturatedConversion;
		use sp_npos_elections::is_score_better;
		use sp_runtime::Perbill;
		impl<T: Trait> Module<T>
		where
			ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
		{
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
			/// Finish the singed phase. Process the signed submissions from best to worse until a valid one
			/// is found, rewarding the best oen and slashing the invalid ones along the way.
			///
			/// Returns true if we have a good solution in the signed phase.
			///
			/// This drains the [`SignedSubmissions`], potentially storing the best valid one in
			/// [`QueuedSolution`].
			pub fn finalize_signed_phase() -> bool {
				let mut all_submission: Vec<SignedSubmission<_, _, _>> =
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
			///
			/// The length of the queue will always be kept less than or equal to `T::MaxSignedSubmissions`.
			pub fn insert_submission(
				who: &T::AccountId,
				queue: &mut Vec<SignedSubmission<T::AccountId, BalanceOf<T>, CompactOf<T>>>,
				solution: RawSolution<CompactOf<T>>,
			) -> Option<usize> {
				let outcome = queue
					.iter()
					.enumerate()
					.rev()
					.find_map(|(i, s)| {
						if is_score_better::<Perbill>(
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
			/// Collect sufficient deposit to store this solution this chain.
			///
			/// The deposit is composed of 3 main elements:
			///
			/// 1. base deposit, fixed for all submissions.
			/// 2. a per-byte deposit, for renting the state usage.
			/// 3. a per-weight deposit, for the potential weight usage in an upcoming on_initialize
			pub fn deposit_for(solution: &RawSolution<CompactOf<T>>) -> BalanceOf<T> {
				let encoded_len: BalanceOf<T> = solution.using_encoded(|e| e.len() as u32).into();
				let feasibility_weight = T::WeightInfo::feasibility_check();
				let len_deposit = T::SignedDepositByte::get() * encoded_len;
				let weight_deposit =
					T::SignedDepositWeight::get() * feasibility_weight.saturated_into();
				T::SignedDepositBase::get() + len_deposit + weight_deposit
			}
			/// The reward for this solution, if successfully chosen as the best one at the end of the
			/// signed phase.
			pub fn reward_for(solution: &RawSolution<CompactOf<T>>) -> BalanceOf<T> {
				T::SignedRewardBase::get()
					+ T::SignedRewardFactor::get()
						* solution.score[0].saturated_into::<BalanceOf<T>>()
			}
		}
	}
	pub mod unsigned {
		//! The unsigned phase implementation.
		use crate::two_phase::*;
		use codec::Encode;
		use sp_arithmetic::traits::SaturatedConversion;
		use sp_npos_elections::is_score_better;
		use sp_runtime::Perbill;
		impl<T: Trait> Module<T> where ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>> {}
	}
	/// The compact solution type used by this crate. This is provided from the [`ElectionDataProvider`]
	/// implementer.
	pub type CompactOf<T> = <<T as Trait>::ElectionDataProvider as ElectionDataProvider<
		<T as frame_system::Trait>::AccountId,
		<T as frame_system::Trait>::BlockNumber,
	>>::CompactSolution;
	/// The voter index. Derived from [`CompactOf`].
	pub type CompactVoterIndexOf<T> = <CompactOf<T> as CompactSolution>::Voter;
	/// The target index. Derived from [`CompactOf`].
	pub type CompactTargetIndexOf<T> = <CompactOf<T> as CompactSolution>::Target;
	/// The accuracy of the election. Derived from [`CompactOf`].
	pub type CompactAccuracyOf<T> = <CompactOf<T> as CompactSolution>::VoteWeight;
	type BalanceOf<T> =
		<<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;
	type PositiveImbalanceOf<T> = <<T as Trait>::Currency as Currency<
		<T as frame_system::Trait>::AccountId,
	>>::PositiveImbalance;
	type NegativeImbalanceOf<T> = <<T as Trait>::Currency as Currency<
		<T as frame_system::Trait>::AccountId,
	>>::NegativeImbalance;
	const LOG_TARGET: &'static str = "two-phase-submission";
	/// Current phase of the pallet.
	pub enum Phase {
		/// Nothing, the election is not happening.
		Off,
		/// Signed phase is open.
		Signed,
		/// Unsigned phase is open.
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
		/// Weather the phase is signed or not.
		pub fn is_signed(&self) -> bool {
			match self {
				Phase::Signed => true,
				_ => false,
			}
		}
		/// Weather the phase is unsigned or not.
		pub fn is_unsigned(&self) -> bool {
			match self {
				Phase::Unsigned(_) => true,
				_ => false,
			}
		}
		/// Weather the phase is unsigned and open or not.
		pub fn is_unsigned_open(&self) -> bool {
			match self {
				Phase::Unsigned(true) => true,
				_ => false,
			}
		}
		/// Weather the phase is off or not.
		pub fn is_off(&self) -> bool {
			match self {
				Phase::Off => true,
				_ => false,
			}
		}
	}
	/// The type of `Computation` that provided this election data.
	pub enum ElectionCompute {
		/// Election was computed on-chain.
		OnChain,
		/// Election was computed with a signed submission.
		Signed,
		/// Election was computed with an unsigned submission.
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
	/// A raw, unchecked solution.
	///
	/// Such a solution should never become effective in anyway before being checked by the
	/// [`Module::feasibility_check`]
	pub struct RawSolution<C> {
		/// Compact election edges.
		compact: C,
		/// The _claimed_ score of the solution.
		score: ElectionScore,
	}
	impl<C> ::core::marker::StructuralPartialEq for RawSolution<C> {}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<C: ::core::cmp::PartialEq> ::core::cmp::PartialEq for RawSolution<C> {
		#[inline]
		fn eq(&self, other: &RawSolution<C>) -> bool {
			match *other {
				RawSolution {
					compact: ref __self_1_0,
					score: ref __self_1_1,
				} => match *self {
					RawSolution {
						compact: ref __self_0_0,
						score: ref __self_0_1,
					} => (*__self_0_0) == (*__self_1_0) && (*__self_0_1) == (*__self_1_1),
				},
			}
		}
		#[inline]
		fn ne(&self, other: &RawSolution<C>) -> bool {
			match *other {
				RawSolution {
					compact: ref __self_1_0,
					score: ref __self_1_1,
				} => match *self {
					RawSolution {
						compact: ref __self_0_0,
						score: ref __self_0_1,
					} => (*__self_0_0) != (*__self_1_0) || (*__self_0_1) != (*__self_1_1),
				},
			}
		}
	}
	impl<C> ::core::marker::StructuralEq for RawSolution<C> {}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<C: ::core::cmp::Eq> ::core::cmp::Eq for RawSolution<C> {
		#[inline]
		#[doc(hidden)]
		fn assert_receiver_is_total_eq(&self) -> () {
			{
				let _: ::core::cmp::AssertParamIsEq<C>;
				let _: ::core::cmp::AssertParamIsEq<ElectionScore>;
			}
		}
	}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<C: ::core::clone::Clone> ::core::clone::Clone for RawSolution<C> {
		#[inline]
		fn clone(&self) -> RawSolution<C> {
			match *self {
				RawSolution {
					compact: ref __self_0_0,
					score: ref __self_0_1,
				} => RawSolution {
					compact: ::core::clone::Clone::clone(&(*__self_0_0)),
					score: ::core::clone::Clone::clone(&(*__self_0_1)),
				},
			}
		}
	}
	const _: () = {
		#[allow(unknown_lints)]
		#[allow(rust_2018_idioms)]
		extern crate codec as _parity_scale_codec;
		impl<C> _parity_scale_codec::Encode for RawSolution<C>
		where
			C: _parity_scale_codec::Encode,
			C: _parity_scale_codec::Encode,
		{
			fn encode_to<EncOut: _parity_scale_codec::Output>(&self, dest: &mut EncOut) {
				dest.push(&self.compact);
				dest.push(&self.score);
			}
		}
		impl<C> _parity_scale_codec::EncodeLike for RawSolution<C>
		where
			C: _parity_scale_codec::Encode,
			C: _parity_scale_codec::Encode,
		{
		}
	};
	const _: () = {
		#[allow(unknown_lints)]
		#[allow(rust_2018_idioms)]
		extern crate codec as _parity_scale_codec;
		impl<C> _parity_scale_codec::Decode for RawSolution<C>
		where
			C: _parity_scale_codec::Decode,
			C: _parity_scale_codec::Decode,
		{
			fn decode<DecIn: _parity_scale_codec::Input>(
				input: &mut DecIn,
			) -> core::result::Result<Self, _parity_scale_codec::Error> {
				Ok(RawSolution {
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
	impl<C> core::fmt::Debug for RawSolution<C>
	where
		C: core::fmt::Debug,
	{
		fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
			fmt.debug_struct("RawSolution")
				.field("compact", &self.compact)
				.field("score", &self.score)
				.finish()
		}
	}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<C: ::core::default::Default> ::core::default::Default for RawSolution<C> {
		#[inline]
		fn default() -> RawSolution<C> {
			RawSolution {
				compact: ::core::default::Default::default(),
				score: ::core::default::Default::default(),
			}
		}
	}
	/// A raw, unchecked signed submission.
	///
	/// This is just a wrapper around [`RawSolution`] and some additional info.
	pub struct SignedSubmission<A, B: HasCompact, C> {
		/// Who submitted this solution.
		who: A,
		/// The deposit reserved for storing this solution.
		deposit: B,
		/// The reward that should be given to this solution, if chosen the as the final one.
		reward: B,
		/// The raw solution itself.
		solution: RawSolution<C>,
	}
	impl<A, B: HasCompact, C> ::core::marker::StructuralPartialEq for SignedSubmission<A, B, C> {}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<
			A: ::core::cmp::PartialEq,
			B: ::core::cmp::PartialEq + HasCompact,
			C: ::core::cmp::PartialEq,
		> ::core::cmp::PartialEq for SignedSubmission<A, B, C>
	{
		#[inline]
		fn eq(&self, other: &SignedSubmission<A, B, C>) -> bool {
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
		fn ne(&self, other: &SignedSubmission<A, B, C>) -> bool {
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
	impl<A, B: HasCompact, C> ::core::marker::StructuralEq for SignedSubmission<A, B, C> {}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<A: ::core::cmp::Eq, B: ::core::cmp::Eq + HasCompact, C: ::core::cmp::Eq> ::core::cmp::Eq
		for SignedSubmission<A, B, C>
	{
		#[inline]
		#[doc(hidden)]
		fn assert_receiver_is_total_eq(&self) -> () {
			{
				let _: ::core::cmp::AssertParamIsEq<A>;
				let _: ::core::cmp::AssertParamIsEq<B>;
				let _: ::core::cmp::AssertParamIsEq<B>;
				let _: ::core::cmp::AssertParamIsEq<RawSolution<C>>;
			}
		}
	}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<
			A: ::core::clone::Clone,
			B: ::core::clone::Clone + HasCompact,
			C: ::core::clone::Clone,
		> ::core::clone::Clone for SignedSubmission<A, B, C>
	{
		#[inline]
		fn clone(&self) -> SignedSubmission<A, B, C> {
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
		impl<A, B: HasCompact, C> _parity_scale_codec::Encode for SignedSubmission<A, B, C>
		where
			A: _parity_scale_codec::Encode,
			A: _parity_scale_codec::Encode,
			B: _parity_scale_codec::Encode,
			B: _parity_scale_codec::Encode,
			B: _parity_scale_codec::Encode,
			B: _parity_scale_codec::Encode,
			RawSolution<C>: _parity_scale_codec::Encode,
			RawSolution<C>: _parity_scale_codec::Encode,
		{
			fn encode_to<EncOut: _parity_scale_codec::Output>(&self, dest: &mut EncOut) {
				dest.push(&self.who);
				dest.push(&self.deposit);
				dest.push(&self.reward);
				dest.push(&self.solution);
			}
		}
		impl<A, B: HasCompact, C> _parity_scale_codec::EncodeLike for SignedSubmission<A, B, C>
		where
			A: _parity_scale_codec::Encode,
			A: _parity_scale_codec::Encode,
			B: _parity_scale_codec::Encode,
			B: _parity_scale_codec::Encode,
			B: _parity_scale_codec::Encode,
			B: _parity_scale_codec::Encode,
			RawSolution<C>: _parity_scale_codec::Encode,
			RawSolution<C>: _parity_scale_codec::Encode,
		{
		}
	};
	const _: () = {
		#[allow(unknown_lints)]
		#[allow(rust_2018_idioms)]
		extern crate codec as _parity_scale_codec;
		impl<A, B: HasCompact, C> _parity_scale_codec::Decode for SignedSubmission<A, B, C>
		where
			A: _parity_scale_codec::Decode,
			A: _parity_scale_codec::Decode,
			B: _parity_scale_codec::Decode,
			B: _parity_scale_codec::Decode,
			B: _parity_scale_codec::Decode,
			B: _parity_scale_codec::Decode,
			RawSolution<C>: _parity_scale_codec::Decode,
			RawSolution<C>: _parity_scale_codec::Decode,
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
	impl<A, B: HasCompact, C> core::fmt::Debug for SignedSubmission<A, B, C>
	where
		A: core::fmt::Debug,
		B: core::fmt::Debug,
		C: core::fmt::Debug,
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
	/// A checked and parsed solution, ready to be enacted.
	pub struct ReadySolution<A> {
		/// The final supports of the solution. This is target-major vector, storing each winners, total
		/// backing, and each individual backer.
		supports: Supports<A>,
		/// How this election was computed.
		compute: ElectionCompute,
	}
	impl<A> ::core::marker::StructuralPartialEq for ReadySolution<A> {}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<A: ::core::cmp::PartialEq> ::core::cmp::PartialEq for ReadySolution<A> {
		#[inline]
		fn eq(&self, other: &ReadySolution<A>) -> bool {
			match *other {
				ReadySolution {
					supports: ref __self_1_0,
					compute: ref __self_1_1,
				} => match *self {
					ReadySolution {
						supports: ref __self_0_0,
						compute: ref __self_0_1,
					} => (*__self_0_0) == (*__self_1_0) && (*__self_0_1) == (*__self_1_1),
				},
			}
		}
		#[inline]
		fn ne(&self, other: &ReadySolution<A>) -> bool {
			match *other {
				ReadySolution {
					supports: ref __self_1_0,
					compute: ref __self_1_1,
				} => match *self {
					ReadySolution {
						supports: ref __self_0_0,
						compute: ref __self_0_1,
					} => (*__self_0_0) != (*__self_1_0) || (*__self_0_1) != (*__self_1_1),
				},
			}
		}
	}
	impl<A> ::core::marker::StructuralEq for ReadySolution<A> {}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<A: ::core::cmp::Eq> ::core::cmp::Eq for ReadySolution<A> {
		#[inline]
		#[doc(hidden)]
		fn assert_receiver_is_total_eq(&self) -> () {
			{
				let _: ::core::cmp::AssertParamIsEq<Supports<A>>;
				let _: ::core::cmp::AssertParamIsEq<ElectionCompute>;
			}
		}
	}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<A: ::core::clone::Clone> ::core::clone::Clone for ReadySolution<A> {
		#[inline]
		fn clone(&self) -> ReadySolution<A> {
			match *self {
				ReadySolution {
					supports: ref __self_0_0,
					compute: ref __self_0_1,
				} => ReadySolution {
					supports: ::core::clone::Clone::clone(&(*__self_0_0)),
					compute: ::core::clone::Clone::clone(&(*__self_0_1)),
				},
			}
		}
	}
	const _: () = {
		#[allow(unknown_lints)]
		#[allow(rust_2018_idioms)]
		extern crate codec as _parity_scale_codec;
		impl<A> _parity_scale_codec::Encode for ReadySolution<A>
		where
			Supports<A>: _parity_scale_codec::Encode,
			Supports<A>: _parity_scale_codec::Encode,
		{
			fn encode_to<EncOut: _parity_scale_codec::Output>(&self, dest: &mut EncOut) {
				dest.push(&self.supports);
				dest.push(&self.compute);
			}
		}
		impl<A> _parity_scale_codec::EncodeLike for ReadySolution<A>
		where
			Supports<A>: _parity_scale_codec::Encode,
			Supports<A>: _parity_scale_codec::Encode,
		{
		}
	};
	const _: () = {
		#[allow(unknown_lints)]
		#[allow(rust_2018_idioms)]
		extern crate codec as _parity_scale_codec;
		impl<A> _parity_scale_codec::Decode for ReadySolution<A>
		where
			Supports<A>: _parity_scale_codec::Decode,
			Supports<A>: _parity_scale_codec::Decode,
		{
			fn decode<DecIn: _parity_scale_codec::Input>(
				input: &mut DecIn,
			) -> core::result::Result<Self, _parity_scale_codec::Error> {
				Ok(ReadySolution {
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
	impl<A> core::fmt::Debug for ReadySolution<A>
	where
		A: core::fmt::Debug,
	{
		fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
			fmt.debug_struct("ReadySolution")
				.field("supports", &self.supports)
				.field("compute", &self.compute)
				.finish()
		}
	}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<A: ::core::default::Default> ::core::default::Default for ReadySolution<A> {
		#[inline]
		fn default() -> ReadySolution<A> {
			ReadySolution {
				supports: ::core::default::Default::default(),
				compute: ::core::default::Default::default(),
			}
		}
	}
	/// The crate errors. Note that this is different from the [`PalletError`].
	pub enum Error {
		/// A feasibility error.
		Feasibility(FeasibilityError),
		/// An error in the on-chain fallback.
		OnChainFallback(crate::onchain::Error),
		/// Snapshot data was unavailable unexpectedly.
		SnapshotUnAvailable,
	}
	impl core::fmt::Debug for Error {
		fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
			match self {
				Self::Feasibility(ref a0) => {
					fmt.debug_tuple("Error::Feasibility").field(a0).finish()
				}
				Self::OnChainFallback(ref a0) => {
					fmt.debug_tuple("Error::OnChainFallback").field(a0).finish()
				}
				Self::SnapshotUnAvailable => fmt.debug_tuple("Error::SnapshotUnAvailable").finish(),
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
				let _: ::core::cmp::AssertParamIsEq<FeasibilityError>;
				let _: ::core::cmp::AssertParamIsEq<crate::onchain::Error>;
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
						(&Error::Feasibility(ref __self_0), &Error::Feasibility(ref __arg_1_0)) => {
							(*__self_0) == (*__arg_1_0)
						}
						(
							&Error::OnChainFallback(ref __self_0),
							&Error::OnChainFallback(ref __arg_1_0),
						) => (*__self_0) == (*__arg_1_0),
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
						(&Error::Feasibility(ref __self_0), &Error::Feasibility(ref __arg_1_0)) => {
							(*__self_0) != (*__arg_1_0)
						}
						(
							&Error::OnChainFallback(ref __self_0),
							&Error::OnChainFallback(ref __arg_1_0),
						) => (*__self_0) != (*__arg_1_0),
						_ => false,
					}
				} else {
					true
				}
			}
		}
	}
	impl From<crate::onchain::Error> for Error {
		fn from(e: crate::onchain::Error) -> Self {
			Error::OnChainFallback(e)
		}
	}
	/// Errors that can happen in the feasibility check.
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
	impl core::fmt::Debug for FeasibilityError {
		fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
			match self {
				Self::WrongWinnerCount => fmt
					.debug_tuple("FeasibilityError::WrongWinnerCount")
					.finish(),
				Self::SnapshotUnavailable => fmt
					.debug_tuple("FeasibilityError::SnapshotUnavailable")
					.finish(),
				Self::NposElectionError(ref a0) => fmt
					.debug_tuple("FeasibilityError::NposElectionError")
					.field(a0)
					.finish(),
				Self::InvalidVote => fmt.debug_tuple("FeasibilityError::InvalidVote").finish(),
				Self::InvalidVoter => fmt.debug_tuple("FeasibilityError::InvalidVoter").finish(),
				Self::InvalidWinner => fmt.debug_tuple("FeasibilityError::InvalidWinner").finish(),
				Self::InvalidScore => fmt.debug_tuple("FeasibilityError::InvalidScore").finish(),
				_ => Ok(()),
			}
		}
	}
	impl ::core::marker::StructuralEq for FeasibilityError {}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl ::core::cmp::Eq for FeasibilityError {
		#[inline]
		#[doc(hidden)]
		fn assert_receiver_is_total_eq(&self) -> () {
			{
				let _: ::core::cmp::AssertParamIsEq<sp_npos_elections::Error>;
			}
		}
	}
	impl ::core::marker::StructuralPartialEq for FeasibilityError {}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl ::core::cmp::PartialEq for FeasibilityError {
		#[inline]
		fn eq(&self, other: &FeasibilityError) -> bool {
			{
				let __self_vi = unsafe { ::core::intrinsics::discriminant_value(&*self) };
				let __arg_1_vi = unsafe { ::core::intrinsics::discriminant_value(&*other) };
				if true && __self_vi == __arg_1_vi {
					match (&*self, &*other) {
						(
							&FeasibilityError::NposElectionError(ref __self_0),
							&FeasibilityError::NposElectionError(ref __arg_1_0),
						) => (*__self_0) == (*__arg_1_0),
						_ => true,
					}
				} else {
					false
				}
			}
		}
		#[inline]
		fn ne(&self, other: &FeasibilityError) -> bool {
			{
				let __self_vi = unsafe { ::core::intrinsics::discriminant_value(&*self) };
				let __arg_1_vi = unsafe { ::core::intrinsics::discriminant_value(&*other) };
				if true && __self_vi == __arg_1_vi {
					match (&*self, &*other) {
						(
							&FeasibilityError::NposElectionError(ref __self_0),
							&FeasibilityError::NposElectionError(ref __arg_1_0),
						) => (*__self_0) != (*__arg_1_0),
						_ => false,
					}
				} else {
					true
				}
			}
		}
	}
	impl From<sp_npos_elections::Error> for FeasibilityError {
		fn from(e: sp_npos_elections::Error) -> Self {
			FeasibilityError::NposElectionError(e)
		}
	}
	/// The weights for this pallet.
	pub trait WeightInfo {
		fn feasibility_check() -> Weight;
		fn submit() -> Weight;
		fn submit_unsigned() -> Weight;
	}
	impl WeightInfo for () {
		fn feasibility_check() -> Weight {
			Default::default()
		}
		fn submit() -> Weight {
			Default::default()
		}
		fn submit_unsigned() -> Weight {
			Default::default()
		}
	}
	pub trait Trait: frame_system::Trait {
		/// Event type.
		type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
		/// Currency type.
		type Currency: ReservableCurrency<Self::AccountId> + Currency<Self::AccountId>;
		/// Duration of the signed phase.
		type SignedPhase: Get<Self::BlockNumber>;
		/// Duration of the unsigned phase.
		type UnsignedPhase: Get<Self::BlockNumber>;
		/// Maximum number of singed submissions that can be queued.
		type MaxSignedSubmissions: Get<u32>;
		type SignedRewardBase: Get<BalanceOf<Self>>;
		type SignedRewardFactor: Get<Perbill>;
		type SignedDepositBase: Get<BalanceOf<Self>>;
		type SignedDepositByte: Get<BalanceOf<Self>>;
		type SignedDepositWeight: Get<BalanceOf<Self>>;
		/// The minimum amount of improvement to the solution score that defines a solution as "better".
		type SolutionImprovementThreshold: Get<Perbill>;
		/// Handler for the slashed deposits.
		type SlashHandler: OnUnbalanced<NegativeImbalanceOf<Self>>;
		/// Handler for the rewards.
		type RewardHandler: OnUnbalanced<PositiveImbalanceOf<Self>>;
		/// Something that will provide the election data.
		type ElectionDataProvider: ElectionDataProvider<Self::AccountId, Self::BlockNumber>;
		/// The weight of the pallet.
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
	impl<T: Trait + 'static> Store for Module<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
		type CurrentPhase = CurrentPhase;
		type SignedSubmissions = SignedSubmissions<T>;
		type QueuedSolution = QueuedSolution<T>;
		type SnapshotTargets = SnapshotTargets<T>;
		type SnapshotVoters = SnapshotVoters<T>;
		type DesiredTargets = DesiredTargets;
	}
	impl<T: Trait + 'static> Module<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
		/// Current phase.
		pub fn current_phase() -> Phase {
			< CurrentPhase < > as self :: sp_api_hidden_includes_decl_storage :: hidden_include :: storage :: StorageValue < Phase > > :: get ( )
		}
		/// Sorted (worse -> best) list of unchecked, signed solutions.
		pub fn signed_submissions(
		) -> Vec<SignedSubmission<T::AccountId, BalanceOf<T>, CompactOf<T>>> {
			< SignedSubmissions < T > as self :: sp_api_hidden_includes_decl_storage :: hidden_include :: storage :: StorageValue < Vec < SignedSubmission < T :: AccountId , BalanceOf < T > , CompactOf < T > > > > > :: get ( )
		}
		/// Current best solution, signed or unsigned.
		pub fn queued_solution() -> Option<ReadySolution<T::AccountId>> {
			< QueuedSolution < T > as self :: sp_api_hidden_includes_decl_storage :: hidden_include :: storage :: StorageValue < ReadySolution < T :: AccountId > > > :: get ( )
		}
		/// Snapshot of all Voters.
		///
		/// This is created at the beginning of the signed phase and cleared upon calling `elect`.
		pub fn snapshot_targets() -> Option<Vec<T::AccountId>> {
			< SnapshotTargets < T > as self :: sp_api_hidden_includes_decl_storage :: hidden_include :: storage :: StorageValue < Vec < T :: AccountId > > > :: get ( )
		}
		/// Snapshot of all targets.
		///
		/// This is created at the beginning of the signed phase and cleared upon calling `elect`.
		pub fn snapshot_voters() -> Option<Vec<(T::AccountId, VoteWeight, Vec<T::AccountId>)>> {
			< SnapshotVoters < T > as self :: sp_api_hidden_includes_decl_storage :: hidden_include :: storage :: StorageValue < Vec < ( T :: AccountId , VoteWeight , Vec < T :: AccountId > ) > > > :: get ( )
		}
		/// Desired number of targets to elect.
		///
		/// This is created at the beginning of the signed phase and cleared upon calling `elect`.
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
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
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
	unsafe impl<T: Trait> Send for __GetByteStructCurrentPhase<T> where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>
	{
	}
	unsafe impl<T: Trait> Sync for __GetByteStructCurrentPhase<T> where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>
	{
	}
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
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
		fn default_byte(
			&self,
		) -> self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::vec::Vec<u8> {
			use self::sp_api_hidden_includes_decl_storage::hidden_include::codec::Encode;
			__CACHE_GET_BYTE_STRUCT_SignedSubmissions . get_or_init ( | | { let def_val : Vec < SignedSubmission < T :: AccountId , BalanceOf < T > , CompactOf < T > > > = Default :: default ( ) ; < Vec < SignedSubmission < T :: AccountId , BalanceOf < T > , CompactOf < T > > > as Encode > :: encode ( & def_val ) } ) . clone ( )
		}
	}
	unsafe impl<T: Trait> Send for __GetByteStructSignedSubmissions<T> where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>
	{
	}
	unsafe impl<T: Trait> Sync for __GetByteStructSignedSubmissions<T> where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>
	{
	}
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
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
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
	unsafe impl<T: Trait> Send for __GetByteStructQueuedSolution<T> where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>
	{
	}
	unsafe impl<T: Trait> Sync for __GetByteStructQueuedSolution<T> where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>
	{
	}
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
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
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
	unsafe impl<T: Trait> Send for __GetByteStructSnapshotTargets<T> where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>
	{
	}
	unsafe impl<T: Trait> Sync for __GetByteStructSnapshotTargets<T> where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>
	{
	}
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
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
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
	unsafe impl<T: Trait> Send for __GetByteStructSnapshotVoters<T> where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>
	{
	}
	unsafe impl<T: Trait> Sync for __GetByteStructSnapshotVoters<T> where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>
	{
	}
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
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
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
	unsafe impl<T: Trait> Send for __GetByteStructDesiredTargets<T> where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>
	{
	}
	unsafe impl<T: Trait> Sync for __GetByteStructDesiredTargets<T> where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>
	{
	}
	impl<T: Trait + 'static> Module<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
		#[doc(hidden)]
		pub fn storage_metadata(
		) -> self::sp_api_hidden_includes_decl_storage::hidden_include::metadata::StorageMetadata {
			self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageMetadata { prefix : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "TwoPhaseElectionProvider" ) , entries : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( & [ self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryMetadata { name : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "CurrentPhase" ) , modifier : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryModifier :: Default , ty : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryType :: Plain ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "Phase" ) ) , default : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DefaultByteGetter ( & __GetByteStructCurrentPhase :: < T > ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: sp_std :: marker :: PhantomData ) ) ) , documentation : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( & [ " Current phase." ] ) , } , self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryMetadata { name : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "SignedSubmissions" ) , modifier : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryModifier :: Default , ty : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryType :: Plain ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "Vec<SignedSubmission<T::AccountId, BalanceOf<T>, CompactOf<T>>>" ) ) , default : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DefaultByteGetter ( & __GetByteStructSignedSubmissions :: < T > ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: sp_std :: marker :: PhantomData ) ) ) , documentation : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( & [ " Sorted (worse -> best) list of unchecked, signed solutions." ] ) , } , self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryMetadata { name : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "QueuedSolution" ) , modifier : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryModifier :: Optional , ty : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryType :: Plain ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "ReadySolution<T::AccountId>" ) ) , default : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DefaultByteGetter ( & __GetByteStructQueuedSolution :: < T > ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: sp_std :: marker :: PhantomData ) ) ) , documentation : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( & [ " Current best solution, signed or unsigned." ] ) , } , self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryMetadata { name : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "SnapshotTargets" ) , modifier : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryModifier :: Optional , ty : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryType :: Plain ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "Vec<T::AccountId>" ) ) , default : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DefaultByteGetter ( & __GetByteStructSnapshotTargets :: < T > ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: sp_std :: marker :: PhantomData ) ) ) , documentation : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( & [ " Snapshot of all Voters." , "" , " This is created at the beginning of the signed phase and cleared upon calling `elect`." ] ) , } , self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryMetadata { name : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "SnapshotVoters" ) , modifier : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryModifier :: Optional , ty : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryType :: Plain ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "Vec<(T::AccountId, VoteWeight, Vec<T::AccountId>)>" ) ) , default : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DefaultByteGetter ( & __GetByteStructSnapshotVoters :: < T > ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: sp_std :: marker :: PhantomData ) ) ) , documentation : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( & [ " Snapshot of all targets." , "" , " This is created at the beginning of the signed phase and cleared upon calling `elect`." ] ) , } , self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryMetadata { name : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "DesiredTargets" ) , modifier : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryModifier :: Default , ty : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: StorageEntryType :: Plain ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( "u32" ) ) , default : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DefaultByteGetter ( & __GetByteStructDesiredTargets :: < T > ( self :: sp_api_hidden_includes_decl_storage :: hidden_include :: sp_std :: marker :: PhantomData ) ) ) , documentation : self :: sp_api_hidden_includes_decl_storage :: hidden_include :: metadata :: DecodeDifferent :: Encode ( & [ " Desired number of targets to elect." , "" , " This is created at the beginning of the signed phase and cleared upon calling `elect`." ] ) , } ] [ .. ] ) , }
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
	/// Sorted (worse -> best) list of unchecked, signed solutions.
	pub struct SignedSubmissions<T: Trait>(
		self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::marker::PhantomData<
				(T,),
			>,
	)
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>;
	impl<T: Trait>
		self::sp_api_hidden_includes_decl_storage::hidden_include::storage::generator::StorageValue<
			Vec<SignedSubmission<T::AccountId, BalanceOf<T>, CompactOf<T>>>,
		> for SignedSubmissions<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
		type Query = Vec<SignedSubmission<T::AccountId, BalanceOf<T>, CompactOf<T>>>;
		fn module_prefix() -> &'static [u8] {
			< __InherentHiddenInstance as self :: sp_api_hidden_includes_decl_storage :: hidden_include :: traits :: Instance > :: PREFIX . as_bytes ( )
		}
		fn storage_prefix() -> &'static [u8] {
			b"SignedSubmissions"
		}
		fn from_optional_value_to_query(
			v: Option<Vec<SignedSubmission<T::AccountId, BalanceOf<T>, CompactOf<T>>>>,
		) -> Self::Query {
			v.unwrap_or_else(|| Default::default())
		}
		fn from_query_to_optional_value(
			v: Self::Query,
		) -> Option<Vec<SignedSubmission<T::AccountId, BalanceOf<T>, CompactOf<T>>>> {
			Some(v)
		}
	}
	/// Current best solution, signed or unsigned.
	pub struct QueuedSolution<T: Trait>(
		self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::marker::PhantomData<
				(T,),
			>,
	)
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>;
	impl<T: Trait>
		self::sp_api_hidden_includes_decl_storage::hidden_include::storage::generator::StorageValue<
			ReadySolution<T::AccountId>,
		> for QueuedSolution<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
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
	/// Snapshot of all Voters.
	///
	/// This is created at the beginning of the signed phase and cleared upon calling `elect`.
	pub struct SnapshotTargets<T: Trait>(
		self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::marker::PhantomData<
				(T,),
			>,
	)
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>;
	impl<T: Trait>
		self::sp_api_hidden_includes_decl_storage::hidden_include::storage::generator::StorageValue<
			Vec<T::AccountId>,
		> for SnapshotTargets<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
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
	/// Snapshot of all targets.
	///
	/// This is created at the beginning of the signed phase and cleared upon calling `elect`.
	pub struct SnapshotVoters<T: Trait>(
		self::sp_api_hidden_includes_decl_storage::hidden_include::sp_std::marker::PhantomData<
				(T,),
			>,
	)
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>;
	impl<T: Trait>
		self::sp_api_hidden_includes_decl_storage::hidden_include::storage::generator::StorageValue<
			Vec<(T::AccountId, VoteWeight, Vec<T::AccountId>)>,
		> for SnapshotVoters<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
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
	/// Desired number of targets to elect.
	///
	/// This is created at the beginning of the signed phase and cleared upon calling `elect`.
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
		/// A solution was stored with the given compute.
		///
		/// If the solution is signed, this means that it hasn't yet been processed. If the solution
		/// is unsigned, this means that it has also been processed.
		SolutionStored(ElectionCompute),
		/// The election has been finalized, with `Some` of the given computation, or else if the
		/// election failed, `None`.
		ElectionFinalized(Option<ElectionCompute>),
		/// An account has been rewarded for their signed submission being finalized.
		Rewarded(AccountId),
		/// An account has been slashed for submitting an invalid signed submission.
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
						r" A solution was stored with the given compute.",
						r"",
						r" If the solution is signed, this means that it hasn't yet been processed. If the solution",
						r" is unsigned, this means that it has also been processed.",
					]),
				},
				::frame_support::event::EventMetadata {
					name: ::frame_support::event::DecodeDifferent::Encode("ElectionFinalized"),
					arguments: ::frame_support::event::DecodeDifferent::Encode(&[
						"Option<ElectionCompute>",
					]),
					documentation: ::frame_support::event::DecodeDifferent::Encode(&[
						r" The election has been finalized, with `Some` of the given computation, or else if the",
						r" election failed, `None`.",
					]),
				},
				::frame_support::event::EventMetadata {
					name: ::frame_support::event::DecodeDifferent::Encode("Rewarded"),
					arguments: ::frame_support::event::DecodeDifferent::Encode(&["AccountId"]),
					documentation: ::frame_support::event::DecodeDifferent::Encode(&[
						r" An account has been rewarded for their signed submission being finalized.",
					]),
				},
				::frame_support::event::EventMetadata {
					name: ::frame_support::event::DecodeDifferent::Encode("Slashed"),
					arguments: ::frame_support::event::DecodeDifferent::Encode(&["AccountId"]),
					documentation: ::frame_support::event::DecodeDifferent::Encode(&[
						r" An account has been slashed for submitting an invalid signed submission.",
					]),
				},
			]
		}
	}
	pub struct Module<T: Trait>(::frame_support::sp_std::marker::PhantomData<(T,)>)
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>;
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<T: ::core::clone::Clone + Trait> ::core::clone::Clone for Module<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
		#[inline]
		fn clone(&self) -> Module<T> {
			match *self {
				Module(ref __self_0_0) => Module(::core::clone::Clone::clone(&(*__self_0_0))),
			}
		}
	}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<T: ::core::marker::Copy + Trait> ::core::marker::Copy for Module<T> where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>
	{
	}
	impl<T: Trait> ::core::marker::StructuralPartialEq for Module<T> where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>
	{
	}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<T: ::core::cmp::PartialEq + Trait> ::core::cmp::PartialEq for Module<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
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
	impl<T: Trait> ::core::marker::StructuralEq for Module<T> where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>
	{
	}
	#[automatically_derived]
	#[allow(unused_qualifications)]
	impl<T: ::core::cmp::Eq + Trait> ::core::cmp::Eq for Module<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
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
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
		T: core::fmt::Debug,
	{
		fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
			fmt.debug_tuple("Module").field(&self.0).finish()
		}
	}
	impl<T: frame_system::Trait + Trait>
		::frame_support::traits::OnInitialize<<T as frame_system::Trait>::BlockNumber> for Module<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
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
								Some(407u32),
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
	impl<T: Trait> ::frame_support::traits::OnRuntimeUpgrade for Module<T> where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>
	{
	}
	impl<T: frame_system::Trait + Trait>
		::frame_support::traits::OnFinalize<<T as frame_system::Trait>::BlockNumber> for Module<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
	}
	impl<T: frame_system::Trait + Trait>
		::frame_support::traits::OffchainWorker<<T as frame_system::Trait>::BlockNumber> for Module<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
		fn offchain_worker(n: T::BlockNumber) {}
	}
	impl<T: Trait> Module<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
		/// Deposits an event using `frame_system::Module::deposit_event`.
		fn deposit_event(event: impl Into<<T as Trait>::Event>) {
			<frame_system::Module<T>>::deposit_event(event.into())
		}
	}
	#[cfg(feature = "std")]
	impl<T: Trait> ::frame_support::traits::IntegrityTest for Module<T> where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>
	{
	}
	/// Can also be called using [`Call`].
	///
	/// [`Call`]: enum.Call.html
	impl<T: Trait> Module<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
		/// Submit a solution for the signed phase.
		///
		/// The dispatch origin fo this call must be __signed__.
		///
		/// The solution potentially queued, based on the claimed score and processed at the end of
		/// the signed phase.
		///
		/// A deposit is reserved and recorded for the solution. Based on the outcome, the solution
		/// might be rewarded, slashed, or get all or a part of the deposit back.
		///
		/// NOTE: Calling this function will bypass origin filters.
		fn submit(
			origin: T::Origin,
			solution: RawSolution<CompactOf<T>>,
		) -> DispatchResultWithPostInfo {
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
								Some(407u32),
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
						return Err("EarlySubmission".into());
					};
				}
			};
			let mut signed_submissions = Self::signed_submissions();
			let maybe_index = Self::insert_submission(&who, &mut signed_submissions, solution);
			{
				if !maybe_index.is_some() {
					{
						return Err("QueueFull".into());
					};
				}
			};
			let index = maybe_index.expect("Option checked to be `Some`; qed.");
			let deposit = signed_submissions[index].deposit;
			T::Currency::reserve(&who, deposit).map_err(|_| "CannotPayDeposit")?;
			if true {
				if !(signed_submissions.len() as u32 <= T::MaxSignedSubmissions::get()) {
					{
						:: std :: rt :: begin_panic ( "assertion failed: signed_submissions.len() as u32 <= T::MaxSignedSubmissions::get()" )
					}
				};
			};
			<SignedSubmissions<T>>::put(signed_submissions);
			Self::deposit_event(RawEvent::SolutionStored(ElectionCompute::Signed));
			Ok(None.into())
		}
		#[allow(unreachable_code)]
		/// Submit a solution for the unsigned phase.
		///
		/// The dispatch origin fo this call must be __signed__.
		///
		/// This submission is checked on the fly, thus it is likely yo be more limited and smaller.
		/// Moreover, this unsigned solution is only validated when submitted to the pool from the
		/// local process. Effectively, this means that only active validators can submit this
		/// transaction when authoring a block.
		///
		/// To prevent any incorrect solution (and thus wasted time/weight), this transaction will
		/// panic if the solution submitted by the validator is invalid, effectively putting their
		/// authoring reward at risk.
		///
		/// No deposit or reward is associated with this.
		///
		/// NOTE: Calling this function will bypass origin filters.
		fn submit_unsigned(
			origin: T::Origin,
			solution: RawSolution<CompactOf<T>>,
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
								Some(407u32),
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
				{
					if !Self::current_phase().is_signed() {
						{
							return Err("EarlySubmission".into());
						};
					}
				};
				use sp_npos_elections::is_score_better;
				if !Self::queued_solution().map_or(true, |q| {
					is_score_better(
						solution.score,
						q.score,
						T::SolutionImprovementThreshold::get(),
					)
				}) {
					{
						::std::rt::begin_panic("WeakSolution")
					}
				};
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
	pub enum Call<T: Trait>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
		#[doc(hidden)]
		#[codec(skip)]
		__PhantomItem(
			::frame_support::sp_std::marker::PhantomData<(T,)>,
			::frame_support::Never,
		),
		#[allow(non_camel_case_types)]
		/// Submit a solution for the signed phase.
		///
		/// The dispatch origin fo this call must be __signed__.
		///
		/// The solution potentially queued, based on the claimed score and processed at the end of
		/// the signed phase.
		///
		/// A deposit is reserved and recorded for the solution. Based on the outcome, the solution
		/// might be rewarded, slashed, or get all or a part of the deposit back.
		submit(RawSolution<CompactOf<T>>),
		#[allow(non_camel_case_types)]
		/// Submit a solution for the unsigned phase.
		///
		/// The dispatch origin fo this call must be __signed__.
		///
		/// This submission is checked on the fly, thus it is likely yo be more limited and smaller.
		/// Moreover, this unsigned solution is only validated when submitted to the pool from the
		/// local process. Effectively, this means that only active validators can submit this
		/// transaction when authoring a block.
		///
		/// To prevent any incorrect solution (and thus wasted time/weight), this transaction will
		/// panic if the solution submitted by the validator is invalid, effectively putting their
		/// authoring reward at risk.
		///
		/// No deposit or reward is associated with this.
		submit_unsigned(RawSolution<CompactOf<T>>),
	}
	const _: () = {
		#[allow(unknown_lints)]
		#[allow(rust_2018_idioms)]
		extern crate codec as _parity_scale_codec;
		impl<T: Trait> _parity_scale_codec::Encode for Call<T>
		where
			ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
			RawSolution<CompactOf<T>>: _parity_scale_codec::Encode,
			RawSolution<CompactOf<T>>: _parity_scale_codec::Encode,
			RawSolution<CompactOf<T>>: _parity_scale_codec::Encode,
			RawSolution<CompactOf<T>>: _parity_scale_codec::Encode,
		{
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
		impl<T: Trait> _parity_scale_codec::EncodeLike for Call<T>
		where
			ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
			RawSolution<CompactOf<T>>: _parity_scale_codec::Encode,
			RawSolution<CompactOf<T>>: _parity_scale_codec::Encode,
			RawSolution<CompactOf<T>>: _parity_scale_codec::Encode,
			RawSolution<CompactOf<T>>: _parity_scale_codec::Encode,
		{
		}
	};
	const _: () = {
		#[allow(unknown_lints)]
		#[allow(rust_2018_idioms)]
		extern crate codec as _parity_scale_codec;
		impl<T: Trait> _parity_scale_codec::Decode for Call<T>
		where
			ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
			RawSolution<CompactOf<T>>: _parity_scale_codec::Decode,
			RawSolution<CompactOf<T>>: _parity_scale_codec::Decode,
			RawSolution<CompactOf<T>>: _parity_scale_codec::Decode,
			RawSolution<CompactOf<T>>: _parity_scale_codec::Decode,
		{
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
	impl<T: Trait> ::frame_support::dispatch::GetDispatchInfo for Call<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
		fn get_dispatch_info(&self) -> ::frame_support::dispatch::DispatchInfo {
			match *self {
				Call::submit(ref solution) => {
					let base_weight = T::WeightInfo::submit();
					let weight = <dyn ::frame_support::dispatch::WeighData<(
						&RawSolution<CompactOf<T>>,
					)>>::weigh_data(&base_weight, (solution,));
					let class = <dyn ::frame_support::dispatch::ClassifyDispatch<(
						&RawSolution<CompactOf<T>>,
					)>>::classify_dispatch(&base_weight, (solution,));
					let pays_fee = <dyn ::frame_support::dispatch::PaysFee<(
						&RawSolution<CompactOf<T>>,
					)>>::pays_fee(&base_weight, (solution,));
					::frame_support::dispatch::DispatchInfo {
						weight,
						class,
						pays_fee,
					}
				}
				Call::submit_unsigned(ref solution) => {
					let base_weight = T::WeightInfo::submit_unsigned();
					let weight = <dyn ::frame_support::dispatch::WeighData<(
						&RawSolution<CompactOf<T>>,
					)>>::weigh_data(&base_weight, (solution,));
					let class = <dyn ::frame_support::dispatch::ClassifyDispatch<(
						&RawSolution<CompactOf<T>>,
					)>>::classify_dispatch(&base_weight, (solution,));
					let pays_fee = <dyn ::frame_support::dispatch::PaysFee<(
						&RawSolution<CompactOf<T>>,
					)>>::pays_fee(&base_weight, (solution,));
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
	impl<T: Trait> ::frame_support::dispatch::GetCallName for Call<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
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
	impl<T: Trait> ::frame_support::dispatch::Clone for Call<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
		fn clone(&self) -> Self {
			match *self {
				Call::submit(ref solution) => Call::submit((*solution).clone()),
				Call::submit_unsigned(ref solution) => Call::submit_unsigned((*solution).clone()),
				_ => ::std::rt::begin_panic("internal error: entered unreachable code"),
			}
		}
	}
	impl<T: Trait> ::frame_support::dispatch::PartialEq for Call<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
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
	impl<T: Trait> ::frame_support::dispatch::Eq for Call<T> where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>
	{
	}
	impl<T: Trait> ::frame_support::dispatch::fmt::Debug for Call<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
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
	impl<T: Trait> ::frame_support::traits::UnfilteredDispatchable for Call<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
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
	impl<T: Trait> ::frame_support::dispatch::Callable<T> for Module<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
		type Call = Call<T>;
	}
	impl<T: Trait> Module<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
		#[doc(hidden)]
		#[allow(dead_code)]
		pub fn call_functions() -> &'static [::frame_support::dispatch::FunctionMetadata] {
			&[
				::frame_support::dispatch::FunctionMetadata {
					name: ::frame_support::dispatch::DecodeDifferent::Encode("submit"),
					arguments: ::frame_support::dispatch::DecodeDifferent::Encode(&[
						::frame_support::dispatch::FunctionArgumentMetadata {
							name: ::frame_support::dispatch::DecodeDifferent::Encode("solution"),
							ty: ::frame_support::dispatch::DecodeDifferent::Encode(
								"RawSolution<CompactOf<T>>",
							),
						},
					]),
					documentation: ::frame_support::dispatch::DecodeDifferent::Encode(&[
						r" Submit a solution for the signed phase.",
						r"",
						r" The dispatch origin fo this call must be __signed__.",
						r"",
						r" The solution potentially queued, based on the claimed score and processed at the end of",
						r" the signed phase.",
						r"",
						r" A deposit is reserved and recorded for the solution. Based on the outcome, the solution",
						r" might be rewarded, slashed, or get all or a part of the deposit back.",
					]),
				},
				::frame_support::dispatch::FunctionMetadata {
					name: ::frame_support::dispatch::DecodeDifferent::Encode("submit_unsigned"),
					arguments: ::frame_support::dispatch::DecodeDifferent::Encode(&[
						::frame_support::dispatch::FunctionArgumentMetadata {
							name: ::frame_support::dispatch::DecodeDifferent::Encode("solution"),
							ty: ::frame_support::dispatch::DecodeDifferent::Encode(
								"RawSolution<CompactOf<T>>",
							),
						},
					]),
					documentation: ::frame_support::dispatch::DecodeDifferent::Encode(&[
						r" Submit a solution for the unsigned phase.",
						r"",
						r" The dispatch origin fo this call must be __signed__.",
						r"",
						r" This submission is checked on the fly, thus it is likely yo be more limited and smaller.",
						r" Moreover, this unsigned solution is only validated when submitted to the pool from the",
						r" local process. Effectively, this means that only active validators can submit this",
						r" transaction when authoring a block.",
						r"",
						r" To prevent any incorrect solution (and thus wasted time/weight), this transaction will",
						r" panic if the solution submitted by the validator is invalid, effectively putting their",
						r" authoring reward at risk.",
						r"",
						r" No deposit or reward is associated with this.",
					]),
				},
			]
		}
	}
	impl<T: 'static + Trait> Module<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
		#[doc(hidden)]
		#[allow(dead_code)]
		pub fn module_constants_metadata(
		) -> &'static [::frame_support::dispatch::ModuleConstantMetadata] {
			&[]
		}
	}
	impl<T: Trait> ::frame_support::dispatch::ModuleErrorMetadata for Module<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
		fn metadata() -> &'static [::frame_support::dispatch::ErrorMetadata] {
			<&'static str as ::frame_support::dispatch::ModuleErrorMetadata>::metadata()
		}
	}
	impl<T: Trait> Module<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
		/// Checks the feasibility of a solution.
		///
		/// This checks the solution for the following:
		///
		/// 0. **all** of the used indices must be correct.
		/// 1. present correct number of winners.
		/// 2. any assignment is checked to match with `SnapshotVoters`.
		/// 3. for each assignment, the check of `ElectionDataProvider` is also examined.
		/// 4. the claimed score is valid.
		fn feasibility_check(
			solution: RawSolution<CompactOf<T>>,
			compute: ElectionCompute,
		) -> Result<ReadySolution<T::AccountId>, FeasibilityError> {
			let RawSolution { compact, score } = solution;
			let winners = compact.unique_targets();
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
			use sp_runtime::traits::UniqueSaturatedInto;
			let voter_at = |i: CompactVoterIndexOf<T>| -> Option<T::AccountId> {
				snapshot_voters
					.get(i.unique_saturated_into())
					.map(|(x, _, _)| x)
					.cloned()
			};
			let target_at = |i: CompactTargetIndexOf<T>| -> Option<T::AccountId> {
				snapshot_targets.get(i.unique_saturated_into()).cloned()
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
									CompactAccuracyOf<T>,
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
			let staked_assignments = assignment_ratio_to_staked_normalized(assignments, stake_of)
				.map_err::<FeasibilityError, _>(Into::into)?;
			let supports = build_support_map(&winners, &staked_assignments)
				.map(FlattenSupportMap::flatten)
				.map_err::<FeasibilityError, _>(Into::into)?;
			let known_score =
				evaluate_support::<T::AccountId, _>(supports.iter().map(|&(ref x, ref y)| (x, y)));
			{
				if !(known_score == score) {
					{
						return Err(FeasibilityError::InvalidScore.into());
					};
				}
			};
			Ok(ReadySolution { supports, compute })
		}
		/// On-chain fallback of election.
		fn onchain_fallback() -> Result<Supports<T::AccountId>, Error> {
			let desired_targets = Self::desired_targets() as usize;
			let voters = Self::snapshot_voters().ok_or(Error::SnapshotUnAvailable)?;
			let targets = Self::snapshot_targets().ok_or(Error::SnapshotUnAvailable)?;
			<OnChainSequentialPhragmen as ElectionProvider<T::AccountId>>::elect::<Perbill>(
				desired_targets,
				targets,
				voters,
			)
			.map_err(Into::into)
		}
	}
	impl<T: Trait> crate::ElectionProvider<T::AccountId> for Module<T>
	where
		ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	{
		type Error = Error;
		const NEEDS_ELECT_DATA: bool = false;
		fn elect<P: PerThing128>(
			_to_elect: usize,
			_targets: Vec<T::AccountId>,
			_voters: Vec<(T::AccountId, VoteWeight, Vec<T::AccountId>)>,
		) -> Result<Supports<T::AccountId>, Self::Error>
		where
			ExtendedBalance: From<<P as PerThing>::Inner>,
		{
			Self::queued_solution()
				.map_or_else(
					|| {
						Self::onchain_fallback()
							.map(|r| (r, ElectionCompute::OnChain))
							.map_err(Into::into)
					},
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
use sp_npos_elections::{CompactSolution, ExtendedBalance, PerThing128, Support, SupportMap};
#[doc(hidden)]
pub use sp_std::convert::TryInto;
/// A flat variant of [`sp_npos_elections::SupportMap`].
///
/// The main advantage of this is that it is encodable.
pub type Supports<A> = Vec<(A, Support<A>)>;
/// Helper trait to convert from a support map to a flat support vector.
pub trait FlattenSupportMap<A> {
	fn flatten(self) -> Supports<A>;
}
impl<A> FlattenSupportMap<A> for SupportMap<A> {
	fn flatten(self) -> Supports<A> {
		self.into_iter().map(|(k, v)| (k, v)).collect::<Vec<_>>()
	}
}
/// Something that can provide the data to something else that implements [`ElectionProvider`], such
/// as the [`two_phase`] module.
///
/// The underlying purpose of this is to provide auxillary data to long-lasting election providers.
/// For example, the [`two_phase`] election provider needs to know the voters/targets list well in
/// advance and before a call to [`ElectionProvider::elect`].
///
/// For example, if pallet A wants to use the two-phase election:
///
/// ```rust,ignore
/// pub trait TraitA {
///     type ElectionProvider: ElectionProvider<_, _>;
/// }
///
/// // these function will be called by `Self::ElectionProvider` whenever needed.
/// impl ElectionDataProvider for PalletA { /* ..  */ }
///
/// impl<T: TraitA> Module<T> {
///     fn do_election() {
///         // finalize the election.
///         T::ElectionProvider::elect( /* .. */ );
///     }
/// }
/// ```
pub trait ElectionDataProvider<AccountId, B> {
	/// The compact solution type.
	///
	/// This should encode the entire solution with the least possible space usage.
	type CompactSolution: codec::Codec + Default + PartialEq + Eq + Clone + Debug + CompactSolution;
	/// All possible targets for the election, i.e. the candidates.
	fn targets() -> Vec<AccountId>;
	/// All possible voters for the election.
	///
	/// Note that if a notion of self-vote exists, it should be represented here.
	fn voters() -> Vec<(AccountId, VoteWeight, Vec<AccountId>)>;
	/// The number of targets to elect.
	fn desired_targets() -> u32;
	/// Check the feasibility of a single assignment for the underlying `ElectionProvider`. In other
	/// words, check if `who` having a weight distribution described as `distribution` is correct or
	/// not.
	///
	/// This might be called by the [`ElectionProvider`] upon processing solutions.
	fn feasibility_check_assignment<P: PerThing>(
		who: &AccountId,
		distribution: &[(AccountId, P)],
	) -> bool;
	/// Provide a best effort prediction about when the next election is about to happen.
	///
	/// In essence, `Self` should predict with this function when it will trigger the
	/// `ElectionDataProvider::elect`.
	fn next_election_prediction(now: B) -> B;
}
/// Something that can compute the result of an election and pass it back to the caller.
pub trait ElectionProvider<AccountId> {
	/// Indicate weather this election provider needs data when calling [`elect`] or not.
	const NEEDS_ELECT_DATA: bool;
	/// The error type that is returned by the provider.
	type Error;
	/// Elect a new set of winners.
	///
	/// The result is returned in a target major format, namely as a support map.
	///
	/// Note that based on the logic of the type that will implement this trait, the input data may
	/// or may not be used. To hint about this to the call site, [`NEEDS_ELECT_DATA`] should be
	/// properly set.
	///
	/// The implementation should, if possible, use the accuracy `P` to compute the election result.
	fn elect<P: PerThing128>(
		to_elect: usize,
		targets: Vec<AccountId>,
		voters: Vec<(AccountId, VoteWeight, Vec<AccountId>)>,
	) -> Result<Supports<AccountId>, Self::Error>
	where
		ExtendedBalance: From<<P as PerThing>::Inner>;
	/// Returns true if an election is still ongoing. This can be used by the call site to
	/// dynamically check of a long-lasting election (such as [`two_phase`]) is still on-going or
	/// not.
	fn ongoing() -> bool;
}
