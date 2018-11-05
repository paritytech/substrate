use substrate_primitives::{ed25519::Pair, hexdisplay::HexDisplay};
use std::fmt;

/// A structure used to carry both Pair and seed.
/// This should usually NOT been used. If unsure, use Pair.
pub struct KeyPair {
	pub pair: Pair,
	pub seed: [u8; 32],
	pub score: f32,
}

// Display to stdout
impl fmt::Display for KeyPair {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, r#"Found match with a score of {:4.2}%
 - Address  : {}
 - Hex seed : 0x{}
 - Seed     : {}"#,
			self.score ,
			self.pair.public().to_ss58check(),
			HexDisplay::from(&self.pair.public().0),
			HexDisplay::from(&self.seed))
    }
}


// Display in a CSV friendly format
impl KeyPair {
	pub fn print_csv(&self) {
		println!("{:5.2}%\t{}\t{}\t{}",
			self.score ,
			self.pair.public().to_ss58check(),
			HexDisplay::from(&self.pair.public().0),
			HexDisplay::from(&self.seed));
    }
}
