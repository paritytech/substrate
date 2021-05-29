use codec::Encode;
use max_encoded_len::MaxEncodedLen;

#[derive(Encode)]
struct NotMel;

#[derive(Encode, MaxEncodedLen)]
enum UnsupportedVariant {
	NotMel(NotMel),
}

fn main() {}
