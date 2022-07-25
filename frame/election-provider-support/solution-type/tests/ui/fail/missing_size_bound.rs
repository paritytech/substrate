use frame_election_provider_solution_type::generate_solution_type;

generate_solution_type!(pub struct TestSolution::<
	VoterIndex = u16,
	TargetIndex = u8,
	Accuracy = Perbill,
	ConstU32::<10>,
>(8));

fn main() {}
