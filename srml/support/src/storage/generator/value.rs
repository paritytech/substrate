#[cfg(not(feature = "std"))]
use sr_std::prelude::*;
use codec::{Codec, Encode, EncodeAppend};
use crate::{storage::{self, unhashed, hashed::{Twox128, StorageHasher}}, rstd::borrow::Borrow};

pub trait StorageValue<T: Codec> {
	/// The type that get/take returns.
	type Query;

	fn key() -> &'static [u8];

	fn from_optional_value_to_query(v: Option<T>) -> Self::Query;

	fn from_query_to_optional_value(v: Self::Query) -> Option<T>;
}

fn storage_value_final_key<T: Codec, S: StorageValue<T>>() -> impl AsRef<[u8]> {
	Twox128::hash(S::key())
}

impl<T: Codec, G: StorageValue<T>> storage::StorageValue<T> for G {
	type Query = G::Query;

	fn key() -> Vec<u8> {
		storage_value_final_key::<_, G>().as_ref().to_vec()
	}

	fn exists() -> bool {
		unhashed::exists(storage_value_final_key::<_, G>().as_ref())
	}

	fn get() -> Self::Query {
		let value = unhashed::get(storage_value_final_key::<_, G>().as_ref());
		G::from_optional_value_to_query(value)
	}

	fn put<Arg: Borrow<T>>(val: Arg) {
		unhashed::put(storage_value_final_key::<_, G>().as_ref(), val.borrow())
	}

	fn put_ref<Arg: ?Sized + Encode>(val: &Arg) where T: AsRef<Arg> {
		val.using_encoded(|b| unhashed::put_raw(storage_value_final_key::<_, G>().as_ref(), b))
	}

	fn kill() {
		unhashed::kill(storage_value_final_key::<_, G>().as_ref())
	}

	fn mutate<R, F: FnOnce(&mut G::Query) -> R>(f: F) -> R {
		// TODO TODO: avoid computing key everytime
		let mut val = G::get();

		let ret = f(&mut val);
		match G::from_query_to_optional_value(val) {
			Some(ref val) => G::put(val),
			None => G::kill(),
		}
		ret
	}

	fn take() -> G::Query {
		let key = storage_value_final_key::<_, G>();
		let value = unhashed::get(key.as_ref());
		if value.is_some() {
			unhashed::kill(key.as_ref())
		}
		G::from_optional_value_to_query(value)
	}

	fn append<I: Encode>(items: &[I]) -> Result<(), &'static str>
		where T: EncodeAppend<Item=I>
	{
		let key = storage_value_final_key::<_, G>();
		let encoded_value = unhashed::get_raw(key.as_ref())
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
		unhashed::put_raw(key.as_ref(), &new_val);
		Ok(())
	}
}
