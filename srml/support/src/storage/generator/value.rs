#[cfg(not(feature = "std"))]
use sr_std::prelude::*;
use codec::{Codec, Encode, EncodeAppend};
use crate::{storage::{self, unhashed, hashed::{Twox128, StorageHasher}}, rstd::borrow::Borrow};

/// Generator for `StorageValue` used by `decl_storage`
pub trait StorageValue<T: Codec> {
	/// The type that get/take returns.
	type Query;

	/// Unhashed key used in storage
	fn key() -> &'static [u8];

	/// Convert an optional value retrieved from storage to the type queried.
	fn from_optional_value_to_query(v: Option<T>) -> Self::Query;

	/// Convert a query to an optional value into storage.
	fn from_query_to_optional_value(v: Self::Query) -> Option<T>;

	/// Generate the full key used in top storage.
	fn storage_value_final_key() -> [u8;16] {
		Twox128::hash(Self::key())
	}
}

impl<T: Codec, G: StorageValue<T>> storage::StorageValue<T> for G {
	type Query = G::Query;

	fn key() -> Vec<u8> {
		Self::storage_value_final_key().to_vec()
	}

	fn exists() -> bool {
		unhashed::exists(&Self::storage_value_final_key())
	}

	fn get() -> Self::Query {
		let value = unhashed::get(&Self::storage_value_final_key());
		G::from_optional_value_to_query(value)
	}

	fn put<Arg: Borrow<T>>(val: Arg) {
		unhashed::put(&Self::storage_value_final_key(), val.borrow())
	}

	fn put_ref<Arg: ?Sized + Encode>(val: &Arg) where T: AsRef<Arg> {
		val.using_encoded(|b| unhashed::put_raw(&Self::storage_value_final_key(), b))
	}

	fn kill() {
		unhashed::kill(&Self::storage_value_final_key())
	}

	fn mutate<R, F: FnOnce(&mut G::Query) -> R>(f: F) -> R {
		let mut val = G::get();

		let ret = f(&mut val);
		match G::from_query_to_optional_value(val) {
			Some(ref val) => G::put(val),
			None => G::kill(),
		}
		ret
	}

	fn take() -> G::Query {
		let key = Self::storage_value_final_key();
		let value = unhashed::get(&key);
		if value.is_some() {
			unhashed::kill(&key)
		}
		G::from_optional_value_to_query(value)
	}

	fn append<I: Encode>(items: &[I]) -> Result<(), &'static str>
		where T: EncodeAppend<Item=I>
	{
		let key = Self::storage_value_final_key();
		let encoded_value = unhashed::get_raw(&key)
			.unwrap_or_else(|| {
				match G::from_query_to_optional_value(G::from_optional_value_to_query(None)) {
					Some(value) => value.encode(),
					None => vec![],
				}
			});

		let new_val = <T as EncodeAppend>::append(
			encoded_value,
			items,
		).map_err(|_| "Could not append given item")?;
		unhashed::put_raw(&key, &new_val);
		Ok(())
	}
}
