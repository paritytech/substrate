use sp_npos_elections_compact::generate_solution_type;

generate_solution_type!(pub struct TestSolution::<
	TargetIndex = u16,
	VoterIndex = u8,
	Accuracy = Perbill,
>(8));

fn main() {}
