use codec::Encode;
use frame_support::traits::MaxEncodedLen;

#[derive(Encode)]
struct NotMel;

#[derive(Encode, MaxEncodedLen)]
enum UnsupportedVariant {
	NotMel(NotMel),
}

fn main() {}
