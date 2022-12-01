use sp_npos_elections_solution_type::generate_solution_type;

generate_solution_type!(pub struct TestSolution::<
	u16,
	u8,
	Perbill,
>(8));

fn main() {}
