use frame_npos_elections_solution_type::generate_solution_type;

generate_solution_type!(pub struct TestSolution::<
	u16,
	TargetIndex = u8,
	Accuracy = Perbill,
	SizeBound = frame_support::traits::ConstU32::<10>,
>(8));

fn main() {}
