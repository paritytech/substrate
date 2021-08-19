use crate::{log, types::*, verifier};
use codec::{Decode, Encode};
use frame_support::{dispatch::Weight, traits::Get};
use sp_runtime::{
	offchain::storage::{MutateStorageError, StorageValueRef},
	traits::SaturatedConversion,
};

pub(crate) struct Miner<T: super::Config>(sp_std::marker::PhantomData<T>);

/// Storage key used to store the last block number at which offchain worker ran.
pub(crate) const OFFCHAIN_LAST_BLOCK: &[u8] = b"parity/multi-phase-unsigned-election";
/// Storage key used to store the offchain worker running status.
pub(crate) const OFFCHAIN_LOCK: &[u8] = b"parity/multi-phase-unsigned-election/lock";
/// Storage key used to cache the solution `call`.
pub(crate) const OFFCHAIN_CACHED_CALL: &[u8] = b"parity/multi-phase-unsigned-election/call";

#[derive(Debug, Eq, PartialEq)]
pub enum MinerError {
	/// An internal error in the NPoS elections crate.
	NposElections(sp_npos_elections::Error),
	/// Snapshot data was unavailable unexpectedly.
	SnapshotUnAvailable,
	/// Submitting a transaction to the pool failed.
	PoolSubmissionFailed,
	/// The snapshot-independent checks failed for the mined solution.
	SnapshotIndependentChecksFailed(sp_runtime::DispatchError),
	/// The solution generated from the miner is not feasible.
	Feasibility(verifier::FeasibilityError),
	/// Something went wrong fetching the lock.
	Lock(&'static str),
	/// Cannot restore a solution that was not stored.
	NoStoredSolution,
	/// Cached solution is not a `submit_unsigned` call.
	SolutionCallInvalid,
	/// Failed to store a solution.
	FailedToStoreSolution,
	/// There are no more voters to remove to trim the solution.
	NoMoreVoters,
}

impl From<sp_npos_elections::Error> for MinerError {
	fn from(e: sp_npos_elections::Error) -> Self {
		MinerError::NposElections(e)
	}
}

impl From<crate::verifier::FeasibilityError> for MinerError {
	fn from(e: verifier::FeasibilityError) -> Self {
		MinerError::Feasibility(e)
	}
}

/// Save a given call into OCW storage.
fn save_solution<T: super::Config>(call: &super::Call<T>) -> Result<(), MinerError> {
	log!(debug, "saving a call to the offchain storage.");
	let storage = StorageValueRef::persistent(&OFFCHAIN_CACHED_CALL);
	match storage.mutate::<_, (), _>(|_| Ok(call.clone())) {
		Ok(_) => Ok(()),
		Err(MutateStorageError::ConcurrentModification(_)) =>
			Err(MinerError::FailedToStoreSolution),
		Err(MutateStorageError::ValueFunctionFailed(_)) => {
			// this branch should be unreachable according to the definition of
			// `StorageValueRef::mutate`: that function should only ever `Err` if the closure we
			// pass it returns an error. however, for safety in case the definition changes, we do
			// not optimize the branch away or panic.
			Err(MinerError::FailedToStoreSolution)
		},
	}
}

/// Get a saved solution from OCW storage if it exists.
fn restore_solution<T: super::Config>() -> Result<super::Call<T>, MinerError> {
	StorageValueRef::persistent(&OFFCHAIN_CACHED_CALL)
		.get()
		.ok()
		.flatten()
		.ok_or(MinerError::NoStoredSolution)
}

/// Clear a saved solution from OCW storage.
pub fn kill_ocw_solution<T: super::Config>() {
	log!(debug, "clearing offchain call cache storage.");
	let mut storage = StorageValueRef::persistent(&OFFCHAIN_CACHED_CALL);
	storage.clear();
}

/// Clear the offchain repeat storage.
///
/// After calling this, the next offchain worker is guaranteed to work, with respect to the
/// frequency repeat.
fn clear_offchain_repeat_frequency() {
	let mut last_block = StorageValueRef::persistent(&OFFCHAIN_LAST_BLOCK);
	last_block.clear();
}

/// `true` when OCW storage contains a solution
#[cfg(test)]
fn ocw_solution_exists<T: super::Config>() -> bool {
	matches!(
		StorageValueRef::persistent(&OFFCHAIN_CACHED_CALL).get::<super::Call<T>>(),
		Ok(Some(_))
	)
}

/// The [`IndexAssignment`][sp_npos_elections::IndexAssignment] type specialized for a particular
/// runtime `T`.
pub type IndexAssignmentOf<T> = sp_npos_elections::IndexAssignmentOf<SolutionOf<T>>;

// TODO: finally make it possible to stick different election algorithms into this guy.
// TODO: now's the time to make sure each solution states the hash of the snapshot.
impl<T: super::Config> Miner<T> {
	/// Attempt to restore a solution from cache. Otherwise, compute it fresh. Either way,
	/// submit if our call's score is greater than that of the cached solution.
	pub fn restore_or_compute_then_maybe_submit() -> Result<(), MinerError> {
		log!(debug, "miner attempting to restore or compute an unsigned solution.");

		let call = restore_solution::<T>()
			.and_then(|call| {
				// ensure the cached call is still current before submitting
				if let super::Call::submit_unsigned(solution, _) = &call {
					// prevent errors arising from state changes in a forkful chain
					Self::full_checks(solution, "restored")?;
					Ok(call)
				} else {
					Err(MinerError::SolutionCallInvalid)
				}
			})
			.or_else::<MinerError, _>(|error| {
				log!(debug, "restoring solution failed due to {:?}", error);
				match error {
					MinerError::NoStoredSolution => {
						log!(trace, "mining a new solution.");
						// if not present or cache invalidated due to feasibility, regenerate.
						// note that failing `Feasibility` can only mean that the solution was
						// computed over a snapshot that has changed due to a fork.
						let call = Self::mine_checked_call()?;
						save_solution(&call)?;
						Ok(call)
					},
					MinerError::Feasibility(_) => {
						log!(trace, "wiping infeasible solution.");
						// kill the infeasible solution, hopefully in the next runs (whenever
						// they may be) we mine a new one.
						kill_ocw_solution::<T>();
						clear_offchain_repeat_frequency();
						Err(error)
					},
					_ => {
						// nothing to do. Return the error as-is.
						Err(error)
					},
				}
			})?;

		Self::submit_call(call)
	}

	/// Mine a new solution, cache it, and submit it back to the chain as an unsigned
	/// transaction.
	pub fn mine_check_save_submit() -> Result<(), MinerError> {
		log!(debug, "miner attempting to compute an unsigned solution.");

		let call = Self::mine_checked_call()?;
		save_solution(&call)?;
		Self::submit_call(call)
	}

	/// Mine a new solution as a call. Performs all checks.
	pub fn mine_checked_call() -> Result<super::Call<T>, MinerError> {
		let iters = Self::get_balancing_iters();
		// get the solution, with a load of checks to ensure if submitted, IT IS ABSOLUTELY
		// VALID.
		let (raw_solution, witness) = Self::mine_and_check(iters)?;

		let score = raw_solution.score.clone();
		let call: super::Call<T> =
			super::Call::submit_unsigned(Box::new(raw_solution), witness).into();

		log!(
			debug,
			"mined a solution with score {:?} and size {}",
			score,
			call.using_encoded(|b| b.len())
		);

		Ok(call)
	}

	fn submit_call(call: super::Call<T>) -> Result<(), MinerError> {
		log!(debug, "miner submitting a solution as an unsigned transaction");
		frame_system::offchain::SubmitTransaction::<T, super::Call<T>>::submit_unsigned_transaction(
			call.into(),
		)
		.map_err(|_| MinerError::PoolSubmissionFailed)
	}

	// perform basic checks of a solution's validity
	//
	// Performance: note that it internally clones the provided solution.
	pub fn full_checks(
		paged_solution: &PagedRawSolution<SolutionOf<T>>,
		solution_type: &str,
	) -> Result<(), MinerError> {
		super::Pallet::<T>::snapshot_independent_checks(paged_solution).map_err(|err| {
			log!(debug, "presnapshot-independent failed for {} solution: {:?}", solution_type, err);
			MinerError::SnapshotIndependentChecksFailed(err)
		})?;

		// check every solution page for feasibility.
		let _ = paged_solution
			.solution_pages
			.iter()
			.enumerate()
			.map(|(page_index, page_solution)| {
				<T::Verifier as verifier::Verifier>::feasibility_check_page(
					page_solution.clone(),
					page_index as PageIndex,
				)
			})
			.collect::<Result<Vec<_>, _>>()
			.map_err(|err| {
				log!(
					debug,
					"feasibility check failed for {} solution at: {:?}",
					solution_type,
					err
				);
				err
			})?;

		Ok(())
	}

	/// Mine a new npos solution, with all the relevant checks to make sure that it will be
	/// accepted to the chain.
	///
	/// If you want an unchecked solution, use [`Pallet::mine_solution`].
	/// If you want a checked solution and submit it at the same time, use
	/// [`Pallet::mine_check_save_submit`].
	pub fn mine_and_check(
		iters: usize,
	) -> Result<(PagedRawSolution<SolutionOf<T>>, SolutionOrSnapshotSize), MinerError> {
		let (paged_solution, witness) = Self::mine_solution(iters)?;
		Self::full_checks(&paged_solution, "mined")?;
		Ok((paged_solution, witness))
	}

	/// Mine a new npos solution.
	pub fn mine_solution(
		iters: usize,
	) -> Result<(PagedRawSolution<SolutionOf<T>>, SolutionOrSnapshotSize), MinerError> {
		todo!()
	}

	/// Convert a raw solution from [`sp_npos_elections::ElectionResult`] to [`RawSolution`],
	/// which is ready to be submitted to the chain.
	///
	/// Will always reduce the solution as well.
	pub fn prepare_election_result(
		election_result: ElectionResult<T::AccountId, SolutionAccuracyOf<T>>,
	) -> Result<(PagedRawSolution<SolutionOf<T>>, SolutionOrSnapshotSize), MinerError> {
		unimplemented!();
		// NOTE: This code path is generally not optimized as it is run offchain. Could use some
		// at some point though.

		// storage items. Note: we have already read this from storage, they must be in cache.
		// let RoundSnapshot { voters, targets } =
		// 	Self::snapshot().ok_or(MinerError::SnapshotUnAvailable)?;
		// let desired_targets =
		// Self::desired_targets().ok_or(MinerError::SnapshotUnAvailable)?;

		// // now make some helper closures.
		// let cache = helpers::generate_voter_cache::<T>(&voters);
		// let voter_index = helpers::voter_index_fn::<T>(&cache);
		// let target_index = helpers::target_index_fn::<T>(&targets);
		// let voter_at = helpers::voter_at_fn::<T>(&voters);
		// let target_at = helpers::target_at_fn::<T>(&targets);
		// let stake_of = helpers::stake_of_fn::<T>(&voters, &cache);

		// // Compute the size of a solution comprised of the selected arguments.
		// //
		// // This function completes in `O(edges)`; it's expensive, but linear.
		// let encoded_size_of = |assignments: &[IndexAssignmentOf<T>]| {
		// 	SolutionOf::<T>::try_from(assignments).map(|s| s.encoded_size())
		// };

		// let ElectionResult { assignments, winners } = election_result;

		// // Reduce (requires round-trip to staked form)
		// let sorted_assignments = {
		// 	// convert to staked and reduce.
		// 	let mut staked = assignment_ratio_to_staked_normalized(assignments, &stake_of)?;

		// 	// we reduce before sorting in order to ensure that the reduction process doesn't
		// 	// accidentally change the sort order
		// 	sp_npos_elections::reduce(&mut staked);

		// 	// Sort the assignments by reversed voter stake. This ensures that we can efficiently
		// 	// truncate the list.
		// 	staked.sort_by_key(
		// 		|sp_npos_elections::StakedAssignment::<T::AccountId> { who, .. }| {
		// 			// though staked assignments are expressed in terms of absolute stake, we'd
		// 			// still need to iterate over all votes in order to actually compute the total
		// 			// stake. it should be faster to look it up from the cache.
		// 			let stake = cache
		// 				.get(who)
		// 				.map(|idx| {
		// 					let (_, stake, _) = voters[*idx];
		// 					stake
		// 				})
		// 				.unwrap_or_default();
		// 			sp_std::cmp::Reverse(stake)
		// 		},
		// 	);

		// 	// convert back.
		// 	assignment_staked_to_ratio_normalized(staked)?
		// };

		// // convert to `IndexAssignment`. This improves the runtime complexity of repeatedly
		// // converting to `Solution`.
		// let mut index_assignments = sorted_assignments
		// 	.into_iter()
		// 	.map(|assignment| IndexAssignmentOf::<T>::new(&assignment, &voter_index,
		// &target_index)) 	.collect::<Result<Vec<_>, _>>()?;

		// // trim assignments list for weight and length.
		// let size =
		// 	SolutionOrSnapshotSize { voters: voters.len() as u32, targets: targets.len() as u32
		// }; Self::trim_assignments_weight(
		// 	desired_targets,
		// 	size,
		// 	T::MinerMaxWeight::get(),
		// 	&mut index_assignments,
		// );
		// Self::trim_assignments_length(
		// 	T::MinerMaxLength::get(),
		// 	&mut index_assignments,
		// 	&encoded_size_of,
		// )?;

		// // now make solution.
		// let solution = SolutionOf::<T>::try_from(&index_assignments)?;

		// // re-calc score.
		// let winners = sp_npos_elections::to_without_backing(winners);
		// let score = solution.clone().score(&winners, stake_of, voter_at, target_at)?;

		// let round = Self::round();
		// Ok((RawSolution { solution, score, round }, size))
	}

	/// Get a random number of iterations to run the balancing in the OCW.
	///
	/// Uses the offchain seed to generate a random number, maxed with
	/// [`Config::MinerMaxIterations`].
	pub fn get_balancing_iters() -> usize {
		use sp_runtime::traits::TrailingZeroInput;
		match T::MinerMaxIterations::get() {
			0 => 0,
			max @ _ => {
				let seed = sp_io::offchain::random_seed();
				let random = <u32>::decode(&mut TrailingZeroInput::new(seed.as_ref()))
					.expect("input is padded with zeroes; qed") %
					max.saturating_add(1);
				random as usize
			},
		}
	}

	/// Greedily reduce the size of the solution to fit into the block w.r.t. weight.
	///
	/// The weight of the solution is foremost a function of the number of voters (i.e.
	/// `assignments.len()`). Aside from this, the other components of the weight are invariant.
	/// The number of winners shall not be changed (otherwise the solution is invalid) and the
	/// `ElectionSize` is merely a representation of the total number of stakers.
	///
	/// Thus, we reside to stripping away some voters from the `assignments`.
	///
	/// Note that the solution is already computed, and the winners are elected based on the
	/// merit of the entire stake in the system. Nonetheless, some of the voters will be removed
	/// further down the line.
	///
	/// Indeed, the score must be computed **after** this step. If this step reduces the score
	/// too much or remove a winner, then the solution must be discarded **after** this step.
	pub fn trim_assignments_weight(
		desired_targets: u32,
		size: SolutionOrSnapshotSize,
		max_weight: Weight,
		assignments: &mut Vec<IndexAssignmentOf<T>>,
	) {
		let maximum_allowed_voters = Self::maximum_voter_for_weight::<
			<T as super::Config>::WeightInfo,
		>(desired_targets, size, max_weight);
		let removing: usize =
			assignments.len().saturating_sub(maximum_allowed_voters.saturated_into());
		log!(
			debug,
			"from {} assignments, truncating to {} for weight, removing {}",
			assignments.len(),
			maximum_allowed_voters,
			removing,
		);
		assignments.truncate(maximum_allowed_voters as usize);
	}

	/// Greedily reduce the size of the solution to fit into the block w.r.t length.
	///
	/// The length of the solution is largely a function of the number of voters. The number of
	/// winners cannot be changed. Thus, to reduce the solution size, we need to strip voters.
	///
	/// Note that this solution is already computed, and winners are elected based on the merit
	/// of the total stake in the system. Nevertheless, some of the voters may be removed here.
	///
	/// Sometimes, removing a voter can cause a validator to also be implicitly removed, if
	/// that voter was the only backer of that winner. In such cases, this solution is invalid,
	/// which will be caught prior to submission.
	///
	/// The score must be computed **after** this step. If this step reduces the score too much,
	/// then the solution must be discarded.
	pub fn trim_assignments_length(
		max_allowed_length: u32,
		assignments: &mut Vec<IndexAssignmentOf<T>>,
		encoded_size_of: impl Fn(&[IndexAssignmentOf<T>]) -> Result<usize, sp_npos_elections::Error>,
	) -> Result<(), MinerError> {
		// Perform a binary search for the max subset of which can fit into the allowed
		// length. Having discovered that, we can truncate efficiently.
		let max_allowed_length: usize = max_allowed_length.saturated_into();
		let mut high = assignments.len();
		let mut low = 0;

		// not much we can do if assignments are already empty.
		if high == low {
			return Ok(())
		}

		while high - low > 1 {
			let test = (high + low) / 2;
			if encoded_size_of(&assignments[..test])? <= max_allowed_length {
				low = test;
			} else {
				high = test;
			}
		}
		let maximum_allowed_voters = if low < assignments.len() &&
			encoded_size_of(&assignments[..low + 1])? <= max_allowed_length
		{
			low + 1
		} else {
			low
		};

		// ensure our post-conditions are correct
		debug_assert!(
			encoded_size_of(&assignments[..maximum_allowed_voters]).unwrap() <= max_allowed_length
		);
		debug_assert!(if maximum_allowed_voters < assignments.len() {
			encoded_size_of(&assignments[..maximum_allowed_voters + 1]).unwrap() >
				max_allowed_length
		} else {
			true
		});

		// NOTE: before this point, every access was immutable.
		// after this point, we never error.
		// check before edit.

		log!(
			debug,
			"from {} assignments, truncating to {} for length, removing {}",
			assignments.len(),
			maximum_allowed_voters,
			assignments.len().saturating_sub(maximum_allowed_voters),
		);
		assignments.truncate(maximum_allowed_voters);

		Ok(())
	}

	/// Find the maximum `len` that a solution can have in order to fit into the block weight.
	///
	/// This only returns a value between zero and `size.nominators`.
	pub fn maximum_voter_for_weight<W: super::WeightInfo>(
		desired_winners: u32,
		size: SolutionOrSnapshotSize,
		max_weight: Weight,
	) -> u32 {
		if size.voters < 1 {
			return size.voters
		}

		let max_voters = size.voters.max(1);
		let mut voters = max_voters;

		// helper closures.
		let weight_with = |active_voters: u32| -> Weight {
			W::submit_unsigned(size.voters, size.targets, active_voters, desired_winners)
		};

		let next_voters = |current_weight: Weight, voters: u32, step: u32| -> Result<u32, ()> {
			use sp_std::cmp::Ordering;
			match current_weight.cmp(&max_weight) {
				Ordering::Less => {
					let next_voters = voters.checked_add(step);
					match next_voters {
						Some(voters) if voters < max_voters => Ok(voters),
						_ => Err(()),
					}
				},
				Ordering::Greater => voters.checked_sub(step).ok_or(()),
				Ordering::Equal => Ok(voters),
			}
		};

		// First binary-search the right amount of voters
		let mut step = voters / 2;
		let mut current_weight = weight_with(voters);

		while step > 0 {
			match next_voters(current_weight, voters, step) {
				// proceed with the binary search
				Ok(next) if next != voters => {
					voters = next;
				},
				// we are out of bounds, break out of the loop.
				Err(()) => break,
				// we found the right value - early exit the function.
				Ok(next) => return next,
			}
			step = step / 2;
			current_weight = weight_with(voters);
		}

		// Time to finish. We might have reduced less than expected due to rounding error.
		// Increase one last time if we have any room left, the reduce until we are sure we are
		// below limit.
		while voters + 1 <= max_voters && weight_with(voters + 1) < max_weight {
			voters += 1;
		}
		while voters.checked_sub(1).is_some() && weight_with(voters) > max_weight {
			voters -= 1;
		}

		let final_decision = voters.min(size.voters);
		debug_assert!(
			weight_with(final_decision) <= max_weight,
			"weight_with({}) <= {}",
			final_decision,
			max_weight,
		);
		final_decision
	}

	/// Checks if an execution of the offchain worker is permitted at the given block number, or
	/// not.
	///
	/// This makes sure that
	/// 1. we don't run on previous blocks in case of a re-org
	/// 2. we don't run twice within a window of length `T::OffchainRepeat`.
	///
	/// Returns `Ok(())` if offchain worker limit is respected, `Err(reason)` otherwise. If
	/// `Ok()` is returned, `now` is written in storage and will be used in further calls as the
	/// baseline.
	pub fn ensure_offchain_repeat_frequency(now: T::BlockNumber) -> Result<(), MinerError> {
		let threshold = T::OffchainRepeat::get();
		let last_block = StorageValueRef::persistent(&OFFCHAIN_LAST_BLOCK);

		let mutate_stat = last_block.mutate::<_, &'static str, _>(
			|maybe_head: Result<Option<T::BlockNumber>, _>| {
				match maybe_head {
					Ok(Some(head)) if now < head => Err("fork."),
					Ok(Some(head)) if now >= head && now <= head + threshold =>
						Err("recently executed."),
					Ok(Some(head)) if now > head + threshold => {
						// we can run again now. Write the new head.
						Ok(now)
					},
					_ => {
						// value doesn't exists. Probably this node just booted up. Write, and
						// run
						Ok(now)
					},
				}
			},
		);

		match mutate_stat {
			// all good
			Ok(_) => Ok(()),
			// failed to write.
			Err(MutateStorageError::ConcurrentModification(_)) =>
				Err(MinerError::Lock("failed to write to offchain db (concurrent modification).")),
			// fork etc.
			Err(MutateStorageError::ValueFunctionFailed(why)) => Err(MinerError::Lock(why)),
		}
	}
}

#[cfg(test)]
mod max_weight_binary_search {
	#![allow(unused_variables)]
	use frame_support::dispatch::Weight;

	use crate::{mock::Runtime, types::SolutionOrSnapshotSize, unsigned::miner::Miner};

	struct TestWeight;
	impl crate::unsigned::WeightInfo for TestWeight {
		fn submit_unsigned(v: u32, t: u32, a: u32, d: u32) -> Weight {
			(0 * v + 0 * t + 1000 * a + 0 * d) as Weight
		}
	}

	#[test]
	fn find_max_voter_binary_search_works() {
		let w = SolutionOrSnapshotSize { voters: 10, targets: 0 };

		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 0), 0);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1), 0);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 999), 0);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1000), 1);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1001), 1);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1990), 1);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1999), 1);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 2000), 2);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 2001), 2);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 2010), 2);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 2990), 2);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 2999), 2);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 3000), 3);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 3333), 3);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 5500), 5);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 7777), 7);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 9999), 9);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 10_000), 10);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 10_999), 10);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 11_000), 10);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 22_000), 10);

		let w = SolutionOrSnapshotSize { voters: 1, targets: 0 };

		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 0), 0);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1), 0);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 999), 0);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1000), 1);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1001), 1);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1990), 1);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1999), 1);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 2000), 1);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 2001), 1);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 2010), 1);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 3333), 1);

		let w = SolutionOrSnapshotSize { voters: 2, targets: 0 };

		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 0), 0);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1), 0);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 999), 0);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1000), 1);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1001), 1);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1999), 1);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 2000), 2);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 2001), 2);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 2010), 2);
		assert_eq!(Miner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 3333), 2);
	}
}
