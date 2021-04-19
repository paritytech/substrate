use std::{
	collections::{HashSet, HashMap},
	convert::TryInto,
	hash::Hash,
};
use sp_npos_elections::{CompactSolution, IndexAssignment};
use rand::{self, Rng, SeedableRng, seq::SliceRandom};

const CANDIDATES: usize = 1000;
const VOTERS: usize = 2500;

sp_npos_elections_compact::generate_solution_type!(
	#[compact]
	pub struct Compact::<VoterIndex = u32, TargetIndex = u16, Accuracy = Accuracy>(16)
);

pub type AccountId = u64;
/// The candidate mask allows easy disambiguation between voters and candidates: accounts
/// for which this bit is set are candidates, and without it, are voters.
pub const CANDIDATE_MASK: AccountId = 1 << ((std::mem::size_of::<AccountId>() * 8) - 1);
pub type CandidateId = AccountId;

pub type Accuracy = sp_runtime::Perbill;

pub type Assignment = sp_npos_elections::Assignment<AccountId, Accuracy>;
pub type Voter = (AccountId, sp_npos_elections::VoteWeight, Vec<AccountId>);

/// Generate voter and assignment lists. Makes no attempt to be realistic about winner or assignment fairness.
///
/// Maintains these invariants:
///
/// - candidate ids have `CANDIDATE_MASK` bit set
/// - voter ids do not have `CANDIDATE_MASK` bit set
/// - assignments have the same ordering as voters
/// - `assignments.distribution.iter().map(|(_, frac)| frac).sum() == One::one()`
/// - a coherent set of winners is chosen.
/// - the winner set is a subset of the candidate set.
/// - `assignments.distribution.iter().all(|(who, _)| winners.contains(who))`
fn generate_random_votes(
	candidate_count: usize,
	voter_count: usize,
	mut rng: impl Rng,
) -> (Vec<Voter>, Vec<Assignment>, Vec<CandidateId>) {
	// cache for fast generation of unique candidate and voter ids
	let mut used_ids = HashSet::with_capacity(candidate_count + voter_count);

	// candidates are easy: just a completely random set of IDs
	let mut candidates: Vec<AccountId> = Vec::with_capacity(candidate_count);
	while candidates.len() < candidate_count {
		let mut new = || rng.gen::<AccountId>() | CANDIDATE_MASK;
		let mut id = new();
		// insert returns `false` when the value was already present
		while !used_ids.insert(id) {
			id = new();
		}
		candidates.push(id);
	}

	// voters are random ids, random weights, random selection from the candidates
	let mut voters = Vec::with_capacity(voter_count);
	while voters.len() < voter_count {
		let mut new = || rng.gen::<AccountId>() & !CANDIDATE_MASK;
		let mut id = new();
		// insert returns `false` when the value was already present
		while !used_ids.insert(id) {
			id = new();
		}

		let vote_weight = rng.gen();

		// it's not interesting if a voter chooses 0 or all candidates, so rule those cases out.
		// also, let's not generate any cases which result in a compact overflow.
		let n_candidates_chosen = rng.gen_range(1, candidates.len().min(16));

		let mut chosen_candidates = Vec::with_capacity(n_candidates_chosen);
		chosen_candidates.extend(candidates.choose_multiple(&mut rng, n_candidates_chosen));
		voters.push((id, vote_weight, chosen_candidates));
	}

	// always generate a sensible number of winners: elections are uninteresting if nobody wins,
	// or everybody wins
	let num_winners = rng.gen_range(1, candidate_count);
	let mut winners: HashSet<AccountId> = HashSet::with_capacity(num_winners);
	winners.extend(candidates.choose_multiple(&mut rng, num_winners));
	assert_eq!(winners.len(), num_winners);

	let mut assignments = Vec::with_capacity(voters.len());
	for (voter_id, _, votes) in voters.iter() {
		let chosen_winners = votes.iter().filter(|vote| winners.contains(vote)).cloned();
		let num_chosen_winners = chosen_winners.clone().count();

		// distribute the available stake randomly
		let stake_distribution = if num_chosen_winners == 0 {
			Vec::new()
		} else {
			let mut available_stake = 1000;
			let mut stake_distribution = Vec::with_capacity(num_chosen_winners);
			for _ in 0..num_chosen_winners - 1 {
				let stake = rng.gen_range(0, available_stake);
				stake_distribution.push(Accuracy::from_perthousand(stake));
				available_stake -= stake;
			}
			stake_distribution.push(Accuracy::from_perthousand(available_stake));
			stake_distribution.shuffle(&mut rng);
			stake_distribution
		};

		assignments.push(Assignment {
			who: *voter_id,
			distribution: chosen_winners.zip(stake_distribution).collect(),
		});
	}

	(voters, assignments, candidates)
}

fn generate_cache<Voters, Item>(voters: Voters) -> HashMap<Item, usize>
where
	Voters: Iterator<Item = Item>,
	Item: Hash + Eq + Copy,
{
	let mut cache = HashMap::new();
	for (idx, voter_id) in voters.enumerate() {
		cache.insert(voter_id, idx);
	}
	cache
}

/// Create a function that returns the index of a voter in the voters list.
pub fn make_voter_fn<VoterIndex>(voters: &[Voter]) -> impl Fn(&AccountId) -> Option<VoterIndex>
where
	usize: TryInto<VoterIndex>,
{
	let cache = generate_cache(voters.iter().map(|(id, _, _)| *id));
	move |who| cache.get(who).cloned().and_then(|i| i.try_into().ok())
}

/// Create a function that returns the index of a candidate in the candidates list.
pub fn make_target_fn<TargetIndex>(
	candidates: &[CandidateId],
) -> impl Fn(&CandidateId) -> Option<TargetIndex>
where
	usize: TryInto<TargetIndex>,
{
	let cache = generate_cache(candidates.iter().cloned());
	move |who| cache.get(who).cloned().and_then(|i| i.try_into().ok())
}

#[test]
fn index_assignments_generate_same_compact_as_plain_assignments() {
	let rng = rand::rngs::SmallRng::seed_from_u64(0);

	let (voters, assignments, candidates) = generate_random_votes(CANDIDATES, VOTERS, rng);
	let voter_index = make_voter_fn(&voters);
	let target_index = make_target_fn(&candidates);

	let compact = Compact::from_assignment(&assignments, &voter_index, &target_index).unwrap();

	let index_assignments = assignments
		.into_iter()
		.map(|assignment| IndexAssignment::new(&assignment, &voter_index, &target_index))
		.collect::<Result<Vec<_>, _>>()
		.unwrap();

	let index_compact = index_assignments.as_slice().try_into().unwrap();

	assert_eq!(compact, index_compact);
}
