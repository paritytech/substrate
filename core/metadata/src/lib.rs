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

use primitive_types::{H160, H256, H512};

use rstd::prelude::*;

use registry::MetadataRegistry;

#[cfg(feature = "std")]
type StringBuf = String;

#[cfg(not(feature = "std"))]
type StringBuf = &'static str;

type MetadataName = Vec<StringBuf>;

#[derive(Clone, PartialEq, Eq)]
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

#[derive(Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub struct EnumVariantMetadata {
	pub name: StringBuf,
	pub index: u32,
	pub fields: Vec<FieldMetadata>
}

#[derive(Encode, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub enum PrimativeMetadata {
	Unknown,
	Unit,
	PhantomData, // do we need this or it can just be Unit?
	Bool,
	Usize, Isize,
	U8, I8,
	U16, I16,
	U32, I32,
	U64, I64,
	U128, I128,
}

impl From<&str> for PrimativeMetadata {
	fn from(x: &str) -> PrimativeMetadata {
		match x {
			"Unit" => PrimativeMetadata::Unit,
			"PhantomData" => PrimativeMetadata::PhantomData,
			"bool" => PrimativeMetadata::Bool,
			"usize" => PrimativeMetadata::Usize,
			"isize" => PrimativeMetadata::Isize,
			"u8" => PrimativeMetadata::U8,
			"i8" => PrimativeMetadata::I8,
			"u16" => PrimativeMetadata::U16,
			"i16" => PrimativeMetadata::I16,
			"u32" => PrimativeMetadata::U32,
			"i32" => PrimativeMetadata::I32,
			"u64" => PrimativeMetadata::U64,
			"i64" => PrimativeMetadata::I64,
			"u128" => PrimativeMetadata::U128,
			"i128" => PrimativeMetadata::I128,
			_ => PrimativeMetadata::Unknown, // panic! can make it runtime error but how to make this compile-time error?
		}
	}
}

#[derive(Encode, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub enum TypeMetadataKind {
	Primative(PrimativeMetadata),
	Array(u32, MetadataName),
	Vector(MetadataName),
	Struct(Vec<FieldMetadata>),
	Enum(Vec<EnumVariantMetadata>),
	Tuple(Vec<MetadataName>),
	Compact,
}

#[derive(Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub struct TypeMetadata {
	pub kind: TypeMetadataKind,
	pub name: MetadataName,
}

pub trait EncodeMetadata {
	fn type_name() -> MetadataName {
		vec!["@Unknown@".into()]
	}

	fn type_metadata_kind(_registry: &mut MetadataRegistry) -> TypeMetadataKind {
		TypeMetadataKind::Primative(PrimativeMetadata::Unknown)
	}

	fn register_type_metadata(registry: &mut MetadataRegistry) {
		let name = Self::type_name();
		registry.register(&name, Self::type_metadata_kind);
	}

	fn type_metadata() -> MetadataRegistry {
		let mut registry = MetadataRegistry::new();
		Self::register_type_metadata(&mut registry);
		registry
	}
}

macro_rules! impl_primatives {
	( $( $t:ty ),* ) => { $(
		impl EncodeMetadata for $t {
			fn type_name() -> MetadataName {
				vec![stringify!($t).into()]
			}

			fn type_metadata_kind(_registry: &mut MetadataRegistry) -> TypeMetadataKind {
				TypeMetadataKind::Primative(stringify!($t).into())
			}
		}
	)* }
}

impl_primatives!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);
impl_primatives!(bool);

macro_rules! impl_array {
	( $( $n:expr )* ) => { $(
		impl<T: EncodeMetadata> EncodeMetadata for [T; $n] {
			fn type_name() -> MetadataName {
				vec!["Array".into(), stringify!($n).into()]
			}

			fn type_metadata_kind(registry: &mut MetadataRegistry) -> TypeMetadataKind {
				let name = T::type_name();
				registry.register(&name, T::type_metadata_kind);
				TypeMetadataKind::Array($n, name)
			}
		}
	)* }
}

impl_array!(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32
	40 48 56 64 72 96 128 160 192 224 256);

impl<T: EncodeMetadata> EncodeMetadata for Vec<T> {
	fn type_name() -> MetadataName {
		let mut name: MetadataName = vec!["Vec".into()];
		name.extend(T::type_name());
		name
	}

	fn type_metadata_kind(registry: &mut MetadataRegistry) -> TypeMetadataKind {
		let name = T::type_name();
		registry.register(&name, T::type_metadata_kind);
		TypeMetadataKind::Vector(name)
	}
}

impl<T: EncodeMetadata> EncodeMetadata for Option<T> {
		fn type_name() -> MetadataName {
		let mut name: MetadataName = vec!["Option".into()];
		name.extend(T::type_name());
		name
	}

	fn type_metadata_kind(registry: &mut MetadataRegistry) -> TypeMetadataKind {
		let name = T::type_name();
		registry.register(&name, T::type_metadata_kind);
		TypeMetadataKind::Enum(vec![
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
						ty: name
					},
				],
			},
		])
	}
}

impl<T: EncodeMetadata, E: EncodeMetadata> EncodeMetadata for Result<T, E> {
	fn type_metadata_kind(registry: &mut MetadataRegistry) -> TypeMetadataKind {
		let name_t = T::type_name();
		let name_e = E::type_name();
		let mut name: MetadataName = vec!["Result".into()];
		name.extend(name_t.clone());
		name.extend(name_e.clone());
		registry.register(&name_t, T::type_metadata_kind);
		registry.register(&name_e, E::type_metadata_kind);

		TypeMetadataKind::Enum(vec![
			EnumVariantMetadata {
				name: "Ok".into(),
				index: 0,
				fields: vec![
					FieldMetadata {
						name: FieldName::Unnamed(0),
						ty: name_t
					},
				],
			},
			EnumVariantMetadata {
				name: "Err".into(),
				index: 1,
				fields: vec![
					FieldMetadata {
						name: FieldName::Unnamed(0),
						ty: name_e
					},
				],
			},
		])
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
		vec!["Compact".into()]
	}

	fn type_metadata_kind(_registry: &mut MetadataRegistry) -> TypeMetadataKind {
		TypeMetadataKind::Compact
	}
}

macro_rules! tuple_impl {
	($one:ident,) => {
		impl<$one: EncodeMetadata> EncodeMetadata for ($one,) {
			fn type_name() -> MetadataName {
				let mut name = vec!["Tuple".into()];
				name.extend(<$one>::type_name());
				name
			}

			fn type_metadata_kind(registry: &mut MetadataRegistry) -> TypeMetadataKind {
				let name = <$one>::type_name();
				registry.register(&name, <$one>::type_metadata_kind);
				TypeMetadataKind::Tuple(vec![name])
			}
		}
	};
	($first:ident, $($rest:ident,)+) => {
		impl<$first: EncodeMetadata, $($rest: EncodeMetadata),+>
		EncodeMetadata for
		($first, $($rest),+) {
			fn type_name() -> MetadataName {
				let mut name = vec!["Tuple".into()];
				name.extend(<$first>::type_name());
				$( name.extend(<$rest>::type_name()); )+
				name
			}

			fn type_metadata_kind(registry: &mut MetadataRegistry) -> TypeMetadataKind {
				let name_first = <$first>::type_name();
				registry.register(&name_first, <$first>::type_metadata_kind);
				let mut vec = vec![name_first];
				$( {
					let name_rest = <$rest>::type_name();
					registry.register(&name_rest, <$rest>::type_metadata_kind);
					vec.push(name_rest);
				} )+
				TypeMetadataKind::Tuple(vec)
			}
		}

		tuple_impl!($($rest,)+);
	}
}

tuple_impl!(A, B, C, D, E, F, G, H, I, J, K,);

impl<T: EncodeMetadata> EncodeMetadata for ::rstd::marker::PhantomData<T> {
	fn type_name() -> MetadataName {
		vec!["PhantomData".into()]
	}

	fn type_metadata_kind(_registry: &mut MetadataRegistry) -> TypeMetadataKind {
		TypeMetadataKind::Primative(PrimativeMetadata::PhantomData)
	}
}

impl EncodeMetadata for () {
	fn type_name() -> MetadataName {
		vec!["Unit".into()]
	}

	fn type_metadata_kind(_registry: &mut MetadataRegistry) -> TypeMetadataKind {
		TypeMetadataKind::Primative(PrimativeMetadata::Unit)
	}
}

impl parity_codec::Encode for FieldName {
	fn encode_to<EncOut: parity_codec::Output>(&self, dest: &mut EncOut) {
		match *self {
			FieldName::Unnamed(ref aa) => {
				dest.push_byte(0usize as u8);
				dest.push(aa);
			}
			FieldName::Named(ref aa) => {
				dest.push_byte(1usize as u8);
				dest.push(aa.as_bytes());
			}
		}
	}
}

impl parity_codec::Encode for EnumVariantMetadata {
	fn encode_to<EncOut: parity_codec::Output>(&self, dest: &mut EncOut) {
		dest.push(&self.name.as_bytes());
		dest.push(&self.index);
		dest.push(&self.fields);
	}
}

impl parity_codec::Encode for TypeMetadata {
	fn encode_to<EncOut: parity_codec::Output>(&self, dest: &mut EncOut) {
		dest.push(&self.kind);
	}
}


impl EncodeMetadata for H160 {
	fn type_name() -> MetadataName {
		<[u8; 20] as EncodeMetadata>::type_name()
	}

	fn type_metadata_kind(registry: &mut MetadataRegistry) -> TypeMetadataKind {
		<[u8; 20] as EncodeMetadata>::type_metadata_kind(registry)
	}
}

impl EncodeMetadata for H256 {
	fn type_name() -> MetadataName {
		<[u8; 32] as EncodeMetadata>::type_name()
	}

	fn type_metadata_kind(registry: &mut MetadataRegistry) -> TypeMetadataKind {
		<[u8; 32] as EncodeMetadata>::type_metadata_kind(registry)
	}
}

impl EncodeMetadata for H512 {
	fn type_name() -> MetadataName {
		<[u8; 64] as EncodeMetadata>::type_name()
	}

	fn type_metadata_kind(registry: &mut MetadataRegistry) -> TypeMetadataKind {
		<[u8; 64] as EncodeMetadata>::type_metadata_kind(registry)
	}
}
