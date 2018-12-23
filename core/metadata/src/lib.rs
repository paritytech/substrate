extern crate parity_codec;
#[macro_use]
extern crate parity_codec_derive;

#[cfg(feature = "std")]
extern crate serde;
#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;

#[derive(Encode, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub enum FieldName {
	Unnamed(u32),
	Named(String),
}

#[derive(Encode, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub struct FieldMetadata {
	pub name: FieldName,
	pub ty: Metadata
}

#[derive(Encode, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub struct EnumVariantMetadata {
	pub name: String,
	pub index: u32,
	pub fields: Vec<FieldMetadata>
}

#[derive(Encode, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub enum TypeMetadata {
	Primative,
	Array(u32, Box<Metadata>),
	Vector(Box<Metadata>),
	Struct(Vec<FieldMetadata>),
	Enum(Vec<EnumVariantMetadata>),
	Tuple(Vec<Metadata>),
}

#[derive(Encode, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub struct Metadata {
	pub name: String,
	pub kind: TypeMetadata
}

pub trait EncodeMetadata {
	fn metadata() -> Metadata;
}

macro_rules! impl_primatives {
	( $( $t:ty ),* ) => { $(
		impl EncodeMetadata for $t {
			fn metadata() -> Metadata {
				Metadata {
					name: stringify!($t).into(),
					kind: TypeMetadata::Primative
				}
			}
		}
	)* }
}

impl_primatives!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);
impl_primatives!(String);

macro_rules! impl_array {
	( $( $n:expr )* ) => { $(
		impl<T: EncodeMetadata> EncodeMetadata for [T; $n] {
			fn metadata() -> Metadata {
				Metadata {
					name: "Array".into(),
					kind: TypeMetadata::Array($n, Box::new(T::metadata()))
				}
			}
		}
	)* }
}

impl_array!(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32
	40 48 56 64 72 96 128 160 192 224 256);

impl<T: EncodeMetadata> EncodeMetadata for Vec<T> {
	fn metadata() -> Metadata {
		Metadata {
			name: "Vec".into(),
			kind: TypeMetadata::Vector(Box::new(T::metadata()))
		}
	}
}

impl<T: EncodeMetadata> EncodeMetadata for Option<T> {
	fn metadata() -> Metadata {
		Metadata {
			name: "Option".into(),
			kind: TypeMetadata::Enum(vec![
				EnumVariantMetadata {
					name: "None".into(),
					index: 0,
					fields: vec![],
				},
				EnumVariantMetadata {
					name: "Some".into(),
					index: 1,
					fields: vec![
						FieldMetadata {
							name: FieldName::Unnamed(0),
							ty: T::metadata()
						},
					],
				},
			])
		}
	}
}

impl<T: EncodeMetadata, E: EncodeMetadata> EncodeMetadata for Result<T, E> {
	fn metadata() -> Metadata {
		Metadata {
			name: "Result".into(),
			kind: TypeMetadata::Enum(vec![
				EnumVariantMetadata {
					name: "Ok".into(),
					index: 0,
					fields: vec![
						FieldMetadata {
							name: FieldName::Unnamed(0),
							ty: T::metadata()
						},
					],
				},
				EnumVariantMetadata {
					name: "Err".into(),
					index: 1,
					fields: vec![
						FieldMetadata {
							name: FieldName::Unnamed(0),
							ty: E::metadata()
						},
					],
				},
			])
		}
	}
}

impl<T: EncodeMetadata> EncodeMetadata for Box<T> {
	fn metadata() -> Metadata {
		T::metadata()
	}
}

impl<T: EncodeMetadata> EncodeMetadata for &T {
	fn metadata() -> Metadata {
		T::metadata()
	}
}

impl<T: EncodeMetadata> EncodeMetadata for [T] {
	fn metadata() -> Metadata {
		<Vec<T>>::metadata()
	}
}

impl<T: EncodeMetadata> EncodeMetadata for parity_codec::Compact<T> {
	fn metadata() -> Metadata {
		T::metadata()
	}
}

macro_rules! tuple_impl {
	($one:ident,) => {
		impl<$one: EncodeMetadata> EncodeMetadata for ($one,) {
			fn metadata() -> Metadata {
				Metadata {
					name: "Tuple".into(),
					kind: TypeMetadata::Tuple(vec![
						<$one>::metadata(),
					]),
				}
			}
		}
	};
	($first:ident, $($rest:ident,)+) => {
		impl<$first: EncodeMetadata, $($rest: EncodeMetadata),+>
		EncodeMetadata for
		($first, $($rest),+) {
			fn metadata() -> Metadata {
				Metadata {
					name: "Tuple".into(),
					kind: TypeMetadata::Tuple(vec![
						<$first>::metadata(),
						$( <$rest>::metadata(), )+
					]),
				}
			}
		}

		tuple_impl!($($rest,)+);
	}
}

tuple_impl!(A, B, C, D, E, F, G, H, I, J, K,);

impl<T: EncodeMetadata> EncodeMetadata for ::std::marker::PhantomData<T> {
	fn metadata() -> Metadata {
		Metadata {
			name: "PhantomData".into(),
			kind: TypeMetadata::Primative
		}
	}
}
