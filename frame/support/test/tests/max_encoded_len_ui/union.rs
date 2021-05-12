use codec::Encode;
use frame_support::traits::MaxEncodedLen;

#[derive(Encode, MaxEncodedLen)]
union Union {
	a: u8,
	b: u16,
}

fn main() {}
