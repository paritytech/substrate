use frame_election_provider_solution_type::generate_solution_type;

generate_solution_type!(pub struct TestSolution::<
	TargetIndex = u16,
	VoterIndex = u8,
	Accuracy = Perbill,
	MaxVoters = ConstU32::<10>,
>(8));

fn main() {}
