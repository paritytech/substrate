use sp_npos_elections_solution_type::generate_solution_type;

generate_solution_type!(pub struct TestSolution::<
	u16,
	TargetIndex = u8,
	Accuracy = Perbill,
>(8));

fn main() {}
