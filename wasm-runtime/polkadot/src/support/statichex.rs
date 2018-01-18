use rustc_hex::FromHex;

pub trait StaticHexConversion: Sized {
	fn from_static_hex(hex: &'static str) -> Self;
}

macro_rules! impl_sizes {
	( $( $t:expr ),* ) => { $(
		impl StaticHexConversion for [u8; $t] {
			fn from_static_hex(hex: &'static str) -> Self {
				let mut r = [0u8; $t];
				r.copy_from_slice(&FromHex::from_hex(hex).unwrap());
				r
			}
		}
	)* }
}

impl_sizes!(1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 20, 24, 28, 32, 40, 48, 56, 64, 80, 96, 112, 128);

pub trait StaticHexInto {
	fn convert<T: StaticHexConversion>(self) -> T;
}

impl StaticHexInto for &'static str {
	fn convert<T: StaticHexConversion>(self) -> T {
		T::from_static_hex(self)
	}
}
