// Copyright 2017-2018 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Tests for the module.

#![cfg(test)]
#![allow(dead_code)]
#![feature(custom_attribute)]

extern crate substrate_metadata;
extern crate substrate_metadata_derive;

use substrate_metadata::*;
use substrate_metadata_derive::EncodeMetadata;


#[derive(Debug, PartialEq, EncodeMetadata)]
struct Unit;

#[derive(Debug, PartialEq, EncodeMetadata)]
struct Indexed(u32, u64);

#[derive(Debug, PartialEq, EncodeMetadata)]
struct Struct<A, B, C> {
	pub a: A,
	pub b: B,
	pub c: C,
}


#[derive(Debug, PartialEq, EncodeMetadata)]
struct StructWithPhantom {
	pub a: u32,
	pub b: u64,
	_c: ::std::marker::PhantomData<u8>,
}

type TestType = Struct<u32, u64, Vec<u8>>;

#[derive(Debug, PartialEq, EncodeMetadata)]
enum EnumType {
	A,
	B(u32, u64),
	C {
		a: u32,
		b: u64,
	},
}

#[derive(Debug, PartialEq, EncodeMetadata)]
enum EnumWithDiscriminant {
	A = 1,
	B = 15,
	C = 255,
}

#[derive(Debug, PartialEq, EncodeMetadata)]
struct StructWithCompact {
	#[codec(compact)]
	pub a: u32,
	pub b: u64,
}


fn get_metadata<T: EncodeMetadata>() -> MetadataRegistry {
	let mut reg = MetadataRegistry::new();
	T::register_type_metadata(&mut reg);
	reg
}

#[test]
fn should_work() {
	assert_eq!(get_metadata::<Unit>(), MetadataRegistry {
		list: vec![
			TypeMetadata {
				name: MetadataName::Custom("mod".into(), "Unit".into()),
				kind: TypeMetadataKind::Struct(Vec::new())
			}
		]
	});
	assert_eq!(get_metadata::<Indexed>(), MetadataRegistry {
		list: vec![
			TypeMetadata {
				name: MetadataName::Custom("mod".into(), "Indexed".into()),
				kind: TypeMetadataKind::Struct(vec![
					FieldMetadata {
						name: FieldName::Unnamed(0),
						ty: MetadataName::U32
					},
					FieldMetadata {
						name: FieldName::Unnamed(1),
						ty: MetadataName::U64
					},
				])
			}
		]
	});
	assert_eq!(get_metadata::<StructWithPhantom>(), MetadataRegistry {
		list: vec![
			TypeMetadata {
				name: MetadataName::Custom("mod".into(), "StructWithPhantom".into()),
				kind: TypeMetadataKind::Struct(vec![
					FieldMetadata {
						name: FieldName::Named("a".into()),
						ty: MetadataName::U32
					},
					FieldMetadata {
						name: FieldName::Named("b".into()),
						ty: MetadataName::U64
					},
					FieldMetadata {
						name: FieldName::Named("_c".into()),
						ty: MetadataName::Unit
					},
				])
			}
		]
	});
	assert_eq!(get_metadata::<TestType>(), MetadataRegistry {
		list: vec![
			TypeMetadata {
				name: MetadataName::CustomWithGenerics("mod".into(), "Struct".into(), vec![
					MetadataName::U32, MetadataName::U64, MetadataName::Vector(Box::new(MetadataName::U8))
				]),
				kind: TypeMetadataKind::Struct(vec![
					FieldMetadata {
						name: FieldName::Named("a".into()),
						ty: MetadataName::U32,
					},
					FieldMetadata {
						name: FieldName::Named("b".into()),
						ty: MetadataName::U64,
					},
					FieldMetadata {
						name: FieldName::Named("c".into()),
						ty: MetadataName::Vector(Box::new(MetadataName::U8)),
					},
				])
			}
		]
	});
	assert_eq!(get_metadata::<EnumWithDiscriminant>(), MetadataRegistry {
		list: vec![
			TypeMetadata {
				name: MetadataName::Custom("mod".into(), "EnumWithDiscriminant".into()),
				kind: TypeMetadataKind::Enum(vec![
					EnumVariantMetadata {
						name: "A".into(),
						index: 1,
						fields: Vec::new(),
					},
					EnumVariantMetadata {
						name: "B".into(),
						index: 15,
						fields: Vec::new(),
					},
					EnumVariantMetadata {
						name: "C".into(),
						index: 255,
						fields: Vec::new(),
					},
				])
			}
		]
	});
	assert_eq!(get_metadata::<Struct<u32, Option<u64>, TestType>>(), MetadataRegistry {
		list: vec![
			TypeMetadata {
				name: MetadataName::CustomWithGenerics("mod".into(), "Struct".into(), vec![
					MetadataName::U32,
					MetadataName::Option(Box::new(MetadataName::U64)),
					MetadataName::CustomWithGenerics("mod".into(), "Struct".into(), vec![
						MetadataName::U32, MetadataName::U64, MetadataName::Vector(Box::new(MetadataName::U8))
					]),
				]),
				kind: TypeMetadataKind::Struct(vec![
					FieldMetadata {
						name: FieldName::Named("a".into()),
						ty: MetadataName::U32,
					},
					FieldMetadata {
						name: FieldName::Named("b".into()),
						ty: MetadataName::Option(Box::new(MetadataName::U64)),
					},
					FieldMetadata {
						name: FieldName::Named("c".into()),
						ty: MetadataName::CustomWithGenerics("mod".into(), "Struct".into(), vec![
							MetadataName::U32, MetadataName::U64, MetadataName::Vector(Box::new(MetadataName::U8))
						]),
					},
				])
			},
			TypeMetadata {
				name: MetadataName::CustomWithGenerics("mod".into(), "Struct".into(), vec![
					MetadataName::U32, MetadataName::U64, MetadataName::Vector(Box::new(MetadataName::U8))
				]),
				kind: TypeMetadataKind::Struct(vec![
					FieldMetadata {
						name: FieldName::Named("a".into()),
						ty: MetadataName::U32,
					},
					FieldMetadata {
						name: FieldName::Named("b".into()),
						ty: MetadataName::U64,
					},
					FieldMetadata {
						name: FieldName::Named("c".into()),
						ty: MetadataName::Vector(Box::new(MetadataName::U8)),
					},
				])
			}
		]
	});
	assert_eq!(get_metadata::<StructWithCompact>(), MetadataRegistry {
		list: vec![
			TypeMetadata {
				name: MetadataName::Custom("mod".into(), "StructWithCompact".into()),
				kind: TypeMetadataKind::Struct(vec![
					FieldMetadata {
						name: FieldName::Named("a".into()),
						ty: MetadataName::Compact(Box::new(MetadataName::U32))
					},
					FieldMetadata {
						name: FieldName::Named("b".into()),
						ty: MetadataName::U64
					},
				])
			}
		]
	});
}
