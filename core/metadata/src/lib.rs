#![cfg_attr(not(feature = "std"), no_std)]

#[cfg_attr(not(feature = "std"), macro_use)]
extern crate sr_std as rstd;

extern crate parity_codec;
#[macro_use]
extern crate parity_codec_derive;

#[cfg(feature = "std")]
extern crate serde;
#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;

extern crate primitive_types;

mod registry;

use primitive_types::{U256, U512, H160, H256, H512};

use rstd::prelude::*;

pub use registry::MetadataRegistry;

#[cfg(feature = "std")]
pub type StringBuf = String;

#[cfg(not(feature = "std"))]
pub type StringBuf = &'static str;

#[derive(Encode, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub enum MetadataName {
	Unknown,
	Compound(Vec<StringBuf>),
	Array(u32, Box<MetadataName>),
	Vector(Box<MetadataName>),
	Tuple(Vec<MetadataName>),
	Option(Box<MetadataName>),
	Result(Box<MetadataName>, Box<MetadataName>),
	Unit,
	Bool,
	Compact, // integer enocded in compac format, the original size doesn't matter
	Usize, Isize,
	U8, I8,
	U16, I16,
	U32, I32,
	U64, I64,
	U128, I128,
	U256,
	U512,
	H160, H256, H512,
}

#[derive(Encode, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub enum FieldName {
	Unnamed(u32),
	Named(StringBuf),
}

#[derive(Encode, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub struct FieldMetadata {
	pub name: FieldName,
	pub ty: MetadataName
}

#[derive(Encode, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub struct EnumVariantMetadata {
	pub name: StringBuf,
	pub index: u32,
	pub fields: Vec<FieldMetadata>
}

#[derive(Encode, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub enum TypeMetadataKind {
	Primative,
	Struct(Vec<FieldMetadata>),
	Enum(Vec<EnumVariantMetadata>),
}

#[derive(Encode, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub struct TypeMetadata {
	pub name: MetadataName,
	pub kind: TypeMetadataKind,
}

pub trait EncodeMetadata {
	fn type_name() -> MetadataName;

	fn type_metadata_kind(registry: &mut MetadataRegistry) -> TypeMetadataKind;

	fn register_type_metadata(registry: &mut MetadataRegistry) {
		registry.register(Self::type_name(), Self::type_metadata_kind);
	}
}

macro_rules! impl_primatives {
	( $( $t:ty => $p:expr, )* ) => { $(
		impl EncodeMetadata for $t {
			fn type_name() -> MetadataName {
				$p
			}

			fn type_metadata_kind(_registry: &mut MetadataRegistry) -> TypeMetadataKind {
				TypeMetadataKind::Primative
			}
		}
	)* }
}

impl_primatives!(
	bool => MetadataName::Bool,
	usize => MetadataName::Usize,
	isize => MetadataName::Isize,
	u8 => MetadataName::U8,
	i8 => MetadataName::I8,
	u16 => MetadataName::U16,
	i16 => MetadataName::I16,
	u32 => MetadataName::U32,
	i32 => MetadataName::I32,
	u64 => MetadataName::U64,
	i64 => MetadataName::I64,
	u128 => MetadataName::U128,
	i128 => MetadataName::I128,
	U256 => MetadataName::U256,
	U512 => MetadataName::U512,
	H160 => MetadataName::H160,
	H256 => MetadataName::H256,
	H512 => MetadataName::H512,
);

macro_rules! impl_array {
	( $( $n:expr )* ) => { $(
		impl<T: EncodeMetadata> EncodeMetadata for [T; $n] {
			fn type_name() -> MetadataName {
				MetadataName::Array($n, Box::new(T::type_name()))
			}

			fn type_metadata_kind(registry: &mut MetadataRegistry) -> TypeMetadataKind {
				registry.register(T::type_name(), T::type_metadata_kind);
				TypeMetadataKind::Primative
			}
		}
	)* }
}

impl_array!(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32
	40 48 56 64 72 96 128 160 192 224 256);

macro_rules! tuple_impl {
	($one:ident,) => {
		impl<$one: EncodeMetadata> EncodeMetadata for ($one,) {
			fn type_name() -> MetadataName {
				MetadataName::Tuple(vec![<$one>::type_name()])
			}

			fn type_metadata_kind(registry: &mut MetadataRegistry) -> TypeMetadataKind {
				registry.register(<$one>::type_name(), <$one>::type_metadata_kind);
				TypeMetadataKind::Primative
			}
		}
	};
	($first:ident, $($rest:ident,)+) => {
		impl<$first: EncodeMetadata, $($rest: EncodeMetadata),+>
		EncodeMetadata for
		($first, $($rest),+) {
			fn type_name() -> MetadataName {
				MetadataName::Tuple(vec![
					<$first>::type_name(),
					$( <$rest>::type_name(), )+
				])
			}

			fn type_metadata_kind(registry: &mut MetadataRegistry) -> TypeMetadataKind {
				registry.register(<$first>::type_name(), <$first>::type_metadata_kind);
				$( {
					registry.register(<$rest>::type_name(), <$rest>::type_metadata_kind);
				} )+
				TypeMetadataKind::Primative
			}
		}

		tuple_impl!($($rest,)+);
	}
}

tuple_impl!(A, B, C, D, E, F, G, H, I, J, K,);

impl<T: EncodeMetadata> EncodeMetadata for Vec<T> {
	fn type_name() -> MetadataName {
		MetadataName::Vector(Box::new(T::type_name()))
	}

	fn type_metadata_kind(registry: &mut MetadataRegistry) -> TypeMetadataKind {
		registry.register(T::type_name(), T::type_metadata_kind);
		TypeMetadataKind::Primative
	}
}

impl<T: EncodeMetadata> EncodeMetadata for Option<T> {
	fn type_name() -> MetadataName {
		MetadataName::Option(Box::new(T::type_name()))
	}

	fn type_metadata_kind(registry: &mut MetadataRegistry) -> TypeMetadataKind {
		registry.register(T::type_name(), T::type_metadata_kind);
		TypeMetadataKind::Primative
	}
}

impl<T: EncodeMetadata, E: EncodeMetadata> EncodeMetadata for Result<T, E> {
	fn type_name() -> MetadataName {
		MetadataName::Result(Box::new(T::type_name()), Box::new(E::type_name()))
	}

	fn type_metadata_kind(registry: &mut MetadataRegistry) -> TypeMetadataKind {
		registry.register(T::type_name(), T::type_metadata_kind);
		registry.register(E::type_name(), E::type_metadata_kind);
		TypeMetadataKind::Primative
	}
}

impl<T: EncodeMetadata> EncodeMetadata for Box<T> {
	fn type_name() -> MetadataName {
		T::type_name()
	}

	fn type_metadata_kind(registry: &mut MetadataRegistry) -> TypeMetadataKind {
		T::type_metadata_kind(registry)
	}
}

impl<T: EncodeMetadata> EncodeMetadata for &T {
	fn type_name() -> MetadataName {
		T::type_name()
	}

	fn type_metadata_kind(registry: &mut MetadataRegistry) -> TypeMetadataKind {
		T::type_metadata_kind(registry)
	}
}

impl<T: EncodeMetadata> EncodeMetadata for [T] {
	fn type_name() -> MetadataName {
		<Vec<T>>::type_name()
	}

	fn type_metadata_kind(registry: &mut MetadataRegistry) -> TypeMetadataKind {
		<Vec<T>>::type_metadata_kind(registry)
	}
}

impl<T: EncodeMetadata> EncodeMetadata for parity_codec::Compact<T> {
	fn type_name() -> MetadataName {
		MetadataName::Compact
	}

	fn type_metadata_kind(_registry: &mut MetadataRegistry) -> TypeMetadataKind {
		TypeMetadataKind::Primative
	}
}

impl<T: EncodeMetadata> EncodeMetadata for ::rstd::marker::PhantomData<T> {
	fn type_name() -> MetadataName {
		MetadataName::Unit
	}

	fn type_metadata_kind(_registry: &mut MetadataRegistry) -> TypeMetadataKind {
		TypeMetadataKind::Primative
	}
}

impl EncodeMetadata for () {
	fn type_name() -> MetadataName {
		MetadataName::Unit
	}

	fn type_metadata_kind(_registry: &mut MetadataRegistry) -> TypeMetadataKind {
		TypeMetadataKind::Primative
	}
}

