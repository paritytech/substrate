pub struct HexDisplay<'a>(&'a [u8]);

impl<'a> HexDisplay<'a> {
	pub fn from(d: &'a AsBytesRef) -> Self { HexDisplay(d.as_bytes_ref()) }
}

impl<'a> ::std::fmt::Display for HexDisplay<'a> {
	fn fmt(&self, fmtr: &mut ::std::fmt::Formatter) -> Result<(), ::std::fmt::Error> {
		for byte in self.0 {
			try!( fmtr.write_fmt(format_args!("{:02x}", byte)));
		}
		Ok(())
	}
}

pub trait AsBytesRef {
	fn as_bytes_ref(&self) -> &[u8];
}

impl AsBytesRef for [u8] {
	fn as_bytes_ref(&self) -> &[u8] { &self }
}

impl AsBytesRef for Vec<u8> {
	fn as_bytes_ref(&self) -> &[u8] { &self }
}

macro_rules! impl_non_endians {
	( $( $t:ty ),* ) => { $(
		impl AsBytesRef for $t {
			fn as_bytes_ref(&self) -> &[u8] { &self[..] }
		}
	)* }
}

impl_non_endians!([u8; 1], [u8; 2], [u8; 3], [u8; 4], [u8; 5], [u8; 6], [u8; 7], [u8; 8],
	[u8; 10], [u8; 12], [u8; 14], [u8; 16], [u8; 20], [u8; 24], [u8; 28], [u8; 32], [u8; 40],
	[u8; 48], [u8; 56], [u8; 64], [u8; 80], [u8; 96], [u8; 112], [u8; 128]);
