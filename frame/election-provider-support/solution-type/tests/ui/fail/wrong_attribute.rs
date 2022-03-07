use frame_npos_elections_solution_type::generate_solution_type;

generate_solution_type!(
	#[pages(1)] pub struct TestSolution::<
		VoterIndex = u8,
		TargetIndex = u16,
		Accuracy = Perbill,
		SizeBound = frame_support::traits::ConstU32::<10>,
	>(8)
);

fn main() {}
