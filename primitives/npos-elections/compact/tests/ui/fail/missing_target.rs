use sp_npos_elections_compact::generate_solution_type;

generate_solution_type!(pub struct TestSolution::<
	VoterIndex = u16,
	u8,
	Accuracy = Perbill,
>(8));

fn main() {}
