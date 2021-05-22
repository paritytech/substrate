use codec::Encode;
use max_encoded_len::MaxEncodedLen;

#[derive(Encode, MaxEncodedLen)]
union Union {
	a: u8,
	b: u16,
}

fn main() {}
