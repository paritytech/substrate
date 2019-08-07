use sr_std::prelude::*;
use codec::{Codec, Encode, EncodeAppend};
use crate::{storage::{self, unhashed, hashed::StorageHasher}, rstd::borrow::Borrow};

pub trait StorageDoubleMap<K1: Encode, K2: Encode, V: Codec> {
	/// The type that get/take returns.
	type Query;

	type Hasher1: StorageHasher;
	type Hasher2: StorageHasher;

	/// Get the prefix key in storage.
	fn key1_prefix() -> &'static [u8];

	// Could we change this just asking for the default value ?
	fn from_optional_value_to_query(v: Option<V>) -> Self::Query;

	fn from_query_to_optional_value(v: Self::Query) -> Option<V>;
}

fn storage_double_map_final_key1<KArg1, K1, K2, V, G>(k1: &KArg1) -> impl AsRef<[u8]>
where
	KArg1: ?Sized + Encode,
	K1: Encode + Borrow<KArg1>,
	K2: Encode,
	V: Codec,
	G: StorageDoubleMap<K1, K2, V>
{
	let mut final_key1 = G::key1_prefix().to_vec();
	k1.encode_to(&mut final_key1);
	G::Hasher1::hash(&final_key1)
}

fn storage_double_map_final_key<KArg1, KArg2, K1, K2, V, G>(k1: &KArg1, k2: &KArg2) -> Vec<u8>
where
	KArg1: ?Sized + Encode,
	KArg2: ?Sized + Encode,
	K1: Encode + Borrow<KArg1>,
	K2: Encode + Borrow<KArg2>,
	V: Codec,
	G: StorageDoubleMap<K1, K2, V>
{
	let mut final_key = storage_double_map_final_key1::<_, _, _, _, G>(k1).as_ref().to_vec();
	final_key.extend_from_slice(k2.using_encoded(G::Hasher2::hash).as_ref());
	final_key
}

impl<K1: Encode, K2: Encode, V: Codec, G: StorageDoubleMap<K1, K2, V>> storage::StorageDoubleMap<K1, K2, V> for G {
	/// The type that get/take returns.
	type Query = G::Query;

	fn exists<KArg1, KArg2>(k1: &KArg1, k2: &KArg2) -> bool
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode
	{
		unhashed::exists(&storage_double_map_final_key::<_, _, _, _, _, G>(k1, k2))
	}

	fn get<KArg1, KArg2>(k1: &KArg1, k2: &KArg2) -> Self::Query
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode
	{
		G::from_optional_value_to_query(unhashed::get(&storage_double_map_final_key::<_, _, _, _, _, G>(k1, k2)))
	}

	fn take<KArg1, KArg2>(k1: &KArg1, k2: &KArg2) -> Self::Query
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode
	{
		let final_key = storage_double_map_final_key::<_, _, _, _, _, G>(k1, k2);

		let value = unhashed::get(&final_key);
		if value.is_some() {
			unhashed::kill(&final_key)
		}
		G::from_optional_value_to_query(value)
	}

	fn insert<KArg1, KArg2, VArg>(k1: &KArg1, k2: &KArg2, val: &VArg)
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		V: Borrow<VArg>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
		VArg: ?Sized + Encode
	{
		unhashed::put(&storage_double_map_final_key::<_, _, _, _, _, G>(k1, k2), &val.borrow())
	}

	fn remove<KArg1, KArg2>(k1: &KArg1, k2: &KArg2)
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode
	{
		unhashed::kill(&storage_double_map_final_key::<_, _, _, _, _, G>(k1, k2))
	}

	fn remove_prefix<KArg1>(k1: &KArg1) where KArg1: ?Sized + Encode, K1: Borrow<KArg1> {
		unhashed::kill_prefix(storage_double_map_final_key1::<_, _, _, _, G>(k1).as_ref())
	}

	fn mutate<KArg1, KArg2, R, F>(k1: &KArg1, k2: &KArg2, f: F) -> R
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
		F: FnOnce(&mut Self::Query) -> R
	{
		// TODO TODO: optimise key computation
		let mut val = G::get(k1, k2);

		let ret = f(&mut val);
		match G::from_query_to_optional_value(val) {
			Some(ref val) => G::insert(k1, k2, val),
			None => G::remove(k1, k2),
		}
		ret
	}

	fn append<KArg1, KArg2, I>(
		k1: &KArg1,
		k2: &KArg2,
		items: &[I],
	) -> Result<(), &'static str>
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
		I: codec::Encode,
		V: EncodeAppend<Item=I>
	{
		let final_key = storage_double_map_final_key::<_, _, _, _, _, G>(k1, k2);

		let encoded_value = unhashed::get_raw(&final_key)
			.unwrap_or_else(|| {
				match G::from_query_to_optional_value(G::from_optional_value_to_query(None)) {
					Some(value) => value.encode(),
					None => vec![],
				}
			});

		let new_val = V::append(
			encoded_value,
			items,
		).ok_or_else(|| "Could not append given item")?;
		unhashed::put_raw(&final_key, &new_val);

		Ok(())
	}
}
