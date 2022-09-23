use codec::Encode;
use frame_support::max_encoded_len::MaxEncodedLen;

#[derive(Encode, MaxEncodedLen)]
#[max_encoded_len_crate(max_encoded_len, frame_support::max_encoded_len)]
struct Example;

fn main() {
	let _ = Example::max_encoded_len();
}
