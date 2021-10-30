use honggfuzz::fuzz;
use sp_npos_elections::{generate_solution_type, sp_arithmetic::Percent};
use sp_runtime::codec::{Encode, Error};

fn main() {
	generate_solution_type!(#[compact] pub struct InnerTestSolutionCompact::<
		VoterIndex = u32,
		TargetIndex = u32,
		Accuracy = Percent,
	>(16));
	loop {
		fuzz!(|fuzzer_data: &[u8]| {
			let result_decoded: Result<InnerTestSolutionCompact, Error> =
				<InnerTestSolutionCompact as codec::Decode>::decode(&mut &fuzzer_data[..]);
			// Ignore errors as not every random sequence of bytes can be decoded as
			// InnerTestSolutionCompact
			if let Ok(decoded) = result_decoded {
				// Decoding works, let's re-encode it and compare results.
				let reencoded: std::vec::Vec<u8> = decoded.encode();
				// The reencoded value may or may not be equal to the original fuzzer output.
				// However, the original decoder should be optimal (in the sense that there is no
				// shorter encoding of the same object). So let's see if the fuzzer can find
				// something shorter:
				if fuzzer_data.len() < reencoded.len() {
					panic!("fuzzer_data.len() < reencoded.len()");
				}
				// The reencoded value should definitely be decodable (if unwrap() fails that is a
				// valid panic/finding for the fuzzer):
				let decoded2: InnerTestSolutionCompact =
					<InnerTestSolutionCompact as codec::Decode>::decode(&mut reencoded.as_slice())
						.unwrap();
				// And it should be equal to the original decoded object (resulting from directly
				// decoding fuzzer_data):
				assert_eq!(decoded, decoded2);
			}
		});
	}
}
