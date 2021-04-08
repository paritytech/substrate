// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#[cfg(test)]
// Do not complain about unused `dispatch` and `dispatch_aux`.
#[allow(dead_code)]
mod tests {
	use frame_support::metadata::*;
	use sp_io::TestExternalities;
	use std::marker::PhantomData;

	frame_support::decl_module! {
		pub struct Module<T: Config> for enum Call where origin: T::Origin, system=frame_support_test {}
	}

	pub trait Config: frame_support_test::Config {}

	frame_support::decl_storage! {
		trait Store for Module<T: Config> as TestStorage {
			// non-getters: pub / $default

			/// Hello, this is doc!
			U32: Option<u32>;
			pub PUBU32: Option<u32>;
			U32MYDEF: Option<u32>;
			pub PUBU32MYDEF: Option<u32>;

			// getters: pub / $default
			// we need at least one type which uses T, otherwise GenesisConfig will complain.
			GETU32 get(fn u32_getter): T::Origin;
			pub PUBGETU32 get(fn pub_u32_getter): u32;
			GETU32WITHCONFIG get(fn u32_getter_with_config) config(): u32;
			pub PUBGETU32WITHCONFIG get(fn pub_u32_getter_with_config) config(): u32;
			GETU32MYDEF get(fn u32_getter_mydef): Option<u32>;
			pub PUBGETU32MYDEF get(fn pub_u32_getter_mydef) config(): u32 = 3;
			GETU32WITHCONFIGMYDEF get(fn u32_getter_with_config_mydef) config(): u32 = 2;
			pub PUBGETU32WITHCONFIGMYDEF get(fn pub_u32_getter_with_config_mydef) config(): u32 = 1;
			PUBGETU32WITHCONFIGMYDEFOPT get(fn pub_u32_getter_with_config_mydef_opt) config(): Option<u32>;

			GetU32WithBuilder get(fn u32_with_builder) build(|_| 1): u32;
			GetOptU32WithBuilderSome get(fn opt_u32_with_builder_some) build(|_| Some(1)): Option<u32>;
			GetOptU32WithBuilderNone get(fn opt_u32_with_builder_none) build(|_| None): Option<u32>;

			// map non-getters: pub / $default
			MAPU32: map hasher(blake2_128_concat) u32 => Option<String>;
			pub PUBMAPU32: map hasher(blake2_128_concat) u32 => Option<String>;
			MAPU32MYDEF: map hasher(blake2_128_concat) u32 => Option<String>;
			pub PUBMAPU32MYDEF: map hasher(blake2_128_concat) u32 => Option<String>;

			// map getters: pub / $default
			GETMAPU32 get(fn map_u32_getter): map hasher(blake2_128_concat) u32 => String;
			pub PUBGETMAPU32 get(fn pub_map_u32_getter): map hasher(blake2_128_concat) u32 => String;

			GETMAPU32MYDEF get(fn map_u32_getter_mydef):
				map hasher(blake2_128_concat) u32 => String = "map".into();
			pub PUBGETMAPU32MYDEF get(fn pub_map_u32_getter_mydef):
				map hasher(blake2_128_concat) u32 => String = "pubmap".into();

			COMPLEXTYPE1: ::std::vec::Vec<T::Origin>;
			COMPLEXTYPE2: (Vec<Vec<(u16, Box<()>)>>, u32);
			COMPLEXTYPE3: [u32; 25];
		}
		add_extra_genesis {
			build(|_| {});
		}
	}

	struct TraitImpl {}

	impl frame_support_test::Config for TraitImpl {
		type Origin = u32;
		type BlockNumber = u32;
		type PalletInfo = frame_support_test::PanicPalletInfo;
		type DbWeight = ();
	}

	impl Config for TraitImpl {}

	const EXPECTED_METADATA: StorageMetadata = StorageMetadata {
		prefix: DecodeDifferent::Encode("TestStorage"),
		entries: DecodeDifferent::Encode(
			&[
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("U32"),
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::Plain(DecodeDifferent::Encode("u32")),
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructU32(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[ " Hello, this is doc!" ]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("PUBU32"),
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::Plain(DecodeDifferent::Encode("u32")),
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructPUBU32(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("U32MYDEF"),
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::Plain(DecodeDifferent::Encode("u32")),
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructU32MYDEF(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("PUBU32MYDEF"),
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::Plain(DecodeDifferent::Encode("u32")),
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructPUBU32MYDEF(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("GETU32"),
					modifier: StorageEntryModifier::Default,
					ty: StorageEntryType::Plain(DecodeDifferent::Encode("T::Origin")),
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructGETU32(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("PUBGETU32"),
					modifier: StorageEntryModifier::Default,
					ty: StorageEntryType::Plain(DecodeDifferent::Encode("u32")),
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructPUBGETU32(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("GETU32WITHCONFIG"),
					modifier: StorageEntryModifier::Default,
					ty: StorageEntryType::Plain(DecodeDifferent::Encode("u32")),
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructGETU32WITHCONFIG(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("PUBGETU32WITHCONFIG"),
					modifier: StorageEntryModifier::Default,
					ty: StorageEntryType::Plain(DecodeDifferent::Encode("u32")),
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructPUBGETU32WITHCONFIG(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("GETU32MYDEF"),
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::Plain(DecodeDifferent::Encode("u32")),
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructGETU32MYDEF(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("PUBGETU32MYDEF"),
					modifier: StorageEntryModifier::Default,
					ty: StorageEntryType::Plain(DecodeDifferent::Encode("u32")),
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructPUBGETU32MYDEF(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("GETU32WITHCONFIGMYDEF"),
					modifier: StorageEntryModifier::Default,
					ty: StorageEntryType::Plain(DecodeDifferent::Encode("u32")),
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructGETU32WITHCONFIGMYDEF(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("PUBGETU32WITHCONFIGMYDEF"),
					modifier: StorageEntryModifier::Default,
					ty: StorageEntryType::Plain(DecodeDifferent::Encode("u32")),
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructPUBGETU32WITHCONFIGMYDEF(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("PUBGETU32WITHCONFIGMYDEFOPT"),
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::Plain(DecodeDifferent::Encode("u32")),
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructPUBGETU32WITHCONFIGMYDEFOPT(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("GetU32WithBuilder"),
					modifier: StorageEntryModifier::Default,
					ty: StorageEntryType::Plain(DecodeDifferent::Encode("u32")),
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructGetU32WithBuilder(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("GetOptU32WithBuilderSome"),
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::Plain(DecodeDifferent::Encode("u32")),
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructGetOptU32WithBuilderSome(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("GetOptU32WithBuilderNone"),
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::Plain(DecodeDifferent::Encode("u32")),
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructGetOptU32WithBuilderNone(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("MAPU32"),
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::Map {
						hasher: StorageHasher::Blake2_128Concat,
						key: DecodeDifferent::Encode("u32"),
						value: DecodeDifferent::Encode("String"),
						unused: false,
					},
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructMAPU32(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("PUBMAPU32"),
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::Map {
						hasher: StorageHasher::Blake2_128Concat,
						key: DecodeDifferent::Encode("u32"),
						value: DecodeDifferent::Encode("String"),
						unused: false,
					},
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructPUBMAPU32(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("MAPU32MYDEF"),
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::Map {
						hasher: StorageHasher::Blake2_128Concat,
						key: DecodeDifferent::Encode("u32"),
						value: DecodeDifferent::Encode("String"),
						unused: false,
					},
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructMAPU32MYDEF(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("PUBMAPU32MYDEF"),
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::Map {
						hasher: StorageHasher::Blake2_128Concat,
						key: DecodeDifferent::Encode("u32"),
						value: DecodeDifferent::Encode("String"),
						unused: false,
					},
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructPUBMAPU32MYDEF(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("GETMAPU32"),
					modifier: StorageEntryModifier::Default,
					ty: StorageEntryType::Map {
						hasher: StorageHasher::Blake2_128Concat,
						key: DecodeDifferent::Encode("u32"),
						value: DecodeDifferent::Encode("String"),
						unused: false,
					},
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructGETMAPU32(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("PUBGETMAPU32"),
					modifier: StorageEntryModifier::Default,
					ty: StorageEntryType::Map {
						hasher: StorageHasher::Blake2_128Concat,
						key: DecodeDifferent::Encode("u32"),
						value: DecodeDifferent::Encode("String"),
						unused: false,
					},
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructPUBGETMAPU32(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("GETMAPU32MYDEF"),
					modifier: StorageEntryModifier::Default,
					ty: StorageEntryType::Map {
						hasher: StorageHasher::Blake2_128Concat,
						key: DecodeDifferent::Encode("u32"),
						value: DecodeDifferent::Encode("String"),
						unused: false,
					},
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructGETMAPU32MYDEF(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("PUBGETMAPU32MYDEF"),
					modifier: StorageEntryModifier::Default,
					ty: StorageEntryType::Map {
						hasher: StorageHasher::Blake2_128Concat,
						key: DecodeDifferent::Encode("u32"),
						value: DecodeDifferent::Encode("String"),
						unused: false,
					},
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructPUBGETMAPU32MYDEF(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("COMPLEXTYPE1"),
					modifier: StorageEntryModifier::Default,
					ty: StorageEntryType::Plain(DecodeDifferent::Encode("::std::vec::Vec<T::Origin>")),
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructCOMPLEXTYPE1(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("COMPLEXTYPE2"),
					modifier: StorageEntryModifier::Default,
					ty: StorageEntryType::Plain(DecodeDifferent::Encode("(Vec<Vec<(u16, Box<()>)>>, u32)")),
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructCOMPLEXTYPE2(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("COMPLEXTYPE3"),
					modifier: StorageEntryModifier::Default,
					ty: StorageEntryType::Plain(DecodeDifferent::Encode("[u32; 25]")),
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructCOMPLEXTYPE3(PhantomData::<TraitImpl>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
			]
		),
	};

	#[test]
	fn store_metadata() {
		let metadata = Module::<TraitImpl>::storage_metadata();
		pretty_assertions::assert_eq!(EXPECTED_METADATA, metadata);
	}

	#[test]
	fn check_genesis_config() {
		let config = GenesisConfig::default();
		assert_eq!(config.u32_getter_with_config, 0u32);
		assert_eq!(config.pub_u32_getter_with_config, 0u32);

		assert_eq!(config.pub_u32_getter_mydef, 3u32);
		assert_eq!(config.u32_getter_with_config_mydef, 2u32);
		assert_eq!(config.pub_u32_getter_with_config_mydef, 1u32);
		assert_eq!(config.pub_u32_getter_with_config_mydef_opt, 0u32);
	}

	#[test]
	fn check_builder_config() {
		let config = GenesisConfig::default();
		let storage = config.build_storage().unwrap();
		TestExternalities::from(storage).execute_with(|| {
			assert_eq!(Module::<TraitImpl>::u32_with_builder(), 1);
			assert_eq!(Module::<TraitImpl>::opt_u32_with_builder_some(), Some(1));
			assert_eq!(Module::<TraitImpl>::opt_u32_with_builder_none(), None);
		})
	}
}

#[cfg(test)]
#[allow(dead_code)]
mod test2 {
	pub trait Config: frame_support_test::Config {}

	frame_support::decl_module! {
		pub struct Module<T: Config> for enum Call where origin: T::Origin, system=frame_support_test {}
	}

	type PairOf<T> = (T, T);

	frame_support::decl_storage! {
		trait Store for Module<T: Config> as TestStorage {
			SingleDef : u32;
			PairDef : PairOf<u32>;
			Single : Option<u32>;
			Pair : (u32, u32);
		}
		add_extra_genesis {
			config(_marker) : ::std::marker::PhantomData<T>;
			config(extra_field) : u32 = 32;
			build(|_| {});
		}
	}

	struct TraitImpl {}

	impl frame_support_test::Config for TraitImpl {
		type Origin = u32;
		type BlockNumber = u32;
		type PalletInfo = frame_support_test::PanicPalletInfo;
		type DbWeight = ();
	}

	impl Config for TraitImpl {}
}

#[cfg(test)]
#[allow(dead_code)]
mod test3 {
	pub trait Config: frame_support_test::Config {}

	frame_support::decl_module! {
		pub struct Module<T: Config> for enum Call where origin: T::Origin, system=frame_support_test {}
	}
	frame_support::decl_storage! {
		trait Store for Module<T: Config> as Test {
			Foo get(fn foo) config(initial_foo): u32;
		}
	}

	type PairOf<T> = (T, T);

	struct TraitImpl {}

	impl frame_support_test::Config for TraitImpl {
		type Origin = u32;
		type BlockNumber = u32;
		type PalletInfo = frame_support_test::PanicPalletInfo;
		type DbWeight = ();
	}

	impl Config for TraitImpl {}
}

#[cfg(test)]
#[allow(dead_code)]
mod test_append_and_len {
	use sp_io::TestExternalities;
	use codec::{Encode, Decode};

	pub trait Config: frame_support_test::Config {}

	frame_support::decl_module! {
		pub struct Module<T: Config> for enum Call where origin: T::Origin, system=frame_support_test {}
	}

	#[derive(PartialEq, Eq, Clone, Encode, Decode)]
	struct NoDef(u32);

	frame_support::decl_storage! {
		trait Store for Module<T: Config> as Test {
			NoDefault: Option<NoDef>;

			JustVec: Vec<u32>;
			JustVecWithDefault: Vec<u32> = vec![6, 9];
			OptionVec: Option<Vec<u32>>;

			MapVec: map hasher(blake2_128_concat) u32 => Vec<u32>;
			MapVecWithDefault: map hasher(blake2_128_concat) u32 => Vec<u32> = vec![6, 9];
			OptionMapVec: map hasher(blake2_128_concat) u32 => Option<Vec<u32>>;

			DoubleMapVec: double_map hasher(blake2_128_concat) u32, hasher(blake2_128_concat) u32 => Vec<u32>;
			DoubleMapVecWithDefault: double_map hasher(blake2_128_concat) u32, hasher(blake2_128_concat) u32 => Vec<u32> = vec![6, 9];
			OptionDoubleMapVec: double_map hasher(blake2_128_concat) u32, hasher(blake2_128_concat) u32 => Option<Vec<u32>>;
		}
	}

	struct Test {}

	impl frame_support_test::Config for Test {
		type Origin = u32;
		type BlockNumber = u32;
		type PalletInfo = frame_support_test::PanicPalletInfo;
		type DbWeight = ();
	}

	impl Config for Test {}

	#[test]
	fn default_for_option() {
		TestExternalities::default().execute_with(|| {
			assert_eq!(OptionVec::get(), None);
			assert!(JustVec::get().is_empty());
		});
	}

	#[test]
	fn append_works() {
		TestExternalities::default().execute_with(|| {
			for val in &[1, 2, 3, 4, 5] {
				MapVec::append(1, val);
			}
			assert_eq!(MapVec::get(1), vec![1, 2, 3, 4, 5]);

			MapVec::remove(1);
			MapVec::append(1, 1);
			assert_eq!(MapVec::get(1), vec![1]);

			for val in &[1, 2, 3, 4, 5] {
				JustVec::append(val);
			}
			assert_eq!(JustVec::get(), vec![1, 2, 3, 4, 5]);

			JustVec::kill();
			JustVec::append(1);
			assert_eq!(JustVec::get(), vec![1]);
		});
	}

	#[test]
	fn append_overwrites_invalid_data() {
		TestExternalities::default().execute_with(|| {
			let key = JustVec::hashed_key();
			// Set it to some invalid value.
			frame_support::storage::unhashed::put_raw(&key, &*b"1");
			assert!(JustVec::get().is_empty());
			assert_eq!(frame_support::storage::unhashed::get_raw(&key), Some(b"1".to_vec()));

			JustVec::append(1);
			JustVec::append(2);
			assert_eq!(JustVec::get(), vec![1, 2]);
		});
	}

	#[test]
	fn append_overwrites_default() {
		TestExternalities::default().execute_with(|| {
			assert_eq!(JustVecWithDefault::get(), vec![6, 9]);
			JustVecWithDefault::append(1);
			assert_eq!(JustVecWithDefault::get(), vec![1]);

			assert_eq!(MapVecWithDefault::get(0), vec![6, 9]);
			MapVecWithDefault::append(0, 1);
			assert_eq!(MapVecWithDefault::get(0), vec![1]);

			assert_eq!(OptionVec::get(), None);
			OptionVec::append(1);
			assert_eq!(OptionVec::get(), Some(vec![1]));
		});
	}

	#[test]
	fn len_works() {
		TestExternalities::default().execute_with(|| {
			JustVec::put(&vec![1, 2, 3, 4]);
			OptionVec::put(&vec![1, 2, 3, 4, 5]);
			MapVec::insert(1, &vec![1, 2, 3, 4, 5, 6]);
			DoubleMapVec::insert(0, 1, &vec![1, 2]);

			assert_eq!(JustVec::decode_len().unwrap(), 4);
			assert_eq!(OptionVec::decode_len().unwrap(), 5);
			assert_eq!(MapVec::decode_len(1).unwrap(), 6);
			assert_eq!(DoubleMapVec::decode_len(0, 1).unwrap(), 2);
		});
	}

	// `decode_len` should always return `None` for default assigments
	// in `decl_storage!`.
	#[test]
	fn len_works_ignores_default_assignment() {
		TestExternalities::default().execute_with(|| {
			// vec
			assert!(JustVec::get().is_empty());
			assert_eq!(JustVec::decode_len(), None);

			assert_eq!(JustVecWithDefault::get(), vec![6, 9]);
			assert_eq!(JustVecWithDefault::decode_len(), None);

			assert_eq!(OptionVec::get(), None);
			assert_eq!(OptionVec::decode_len(), None);

			// map
			assert!(MapVec::get(0).is_empty());
			assert_eq!(MapVec::decode_len(0), None);

			assert_eq!(MapVecWithDefault::get(0), vec![6, 9]);
			assert_eq!(MapVecWithDefault::decode_len(0), None);

			assert_eq!(OptionMapVec::get(0), None);
			assert_eq!(OptionMapVec::decode_len(0), None);

			// Double map
			assert!(DoubleMapVec::get(0, 0).is_empty());
			assert_eq!(DoubleMapVec::decode_len(0, 1), None);

			assert_eq!(DoubleMapVecWithDefault::get(0, 0), vec![6, 9]);
			assert_eq!(DoubleMapVecWithDefault::decode_len(0, 1), None);

			assert_eq!(OptionDoubleMapVec::get(0, 0), None);
			assert_eq!(OptionDoubleMapVec::decode_len(0, 1), None);
		});
	}
}
