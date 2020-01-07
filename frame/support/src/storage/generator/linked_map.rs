// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

use codec::{FullCodec, Encode, Decode, EncodeLike, Ref};
use crate::{storage::{self, unhashed}, hash::{StorageHasher, Twox128}, traits::Len};
use sp_std::{prelude::*, marker::PhantomData};

/// Generator for `StorageLinkedMap` used by `decl_storage`.
///
/// By default final key generation rely on `KeyFormat`.
pub trait StorageLinkedMap<K: FullCodec, V: FullCodec> {
	/// The type that get/take returns.
	type Query;

	/// The family of key formats used for this map.
	type KeyFormat: KeyFormat;

	/// Convert an optional value retrieved from storage to the type queried.
	fn from_optional_value_to_query(v: Option<V>) -> Self::Query;

	/// Convert a query to an optional value into storage.
	fn from_query_to_optional_value(v: Self::Query) -> Option<V>;

	/// Generate the full key used in top storage.
	fn storage_linked_map_final_key<KeyArg>(key: KeyArg) -> Vec<u8>
	where
		KeyArg: EncodeLike<K>,
	{
		<Self::KeyFormat as KeyFormat>::storage_linked_map_final_key::<KeyArg>(&key)
	}

	/// Generate the hashed key for head
	fn storage_linked_map_final_head_key() -> Vec<u8> {
		<Self::KeyFormat as KeyFormat>::storage_linked_map_final_head_key()
	}
}

/// A type-abstracted key format used for a family of linked-map types.
///
/// # Default mapping of keys to a storage path
///
/// The key for the head of the map is stored at one fixed path:
/// ```nocompile
/// Twox128(module_prefix) ++ Twox128(head_prefix)
/// ```
///
/// For each key, the value stored under that key is appended with a
/// [`Linkage`](struct.Linkage.html) (which hold previous and next key) at the path:
/// ```nocompile
/// Twox128(module_prefix) ++ Twox128(storage_prefix) ++ Hasher(encode(key))
/// ```
///
/// Enumeration is done by getting the head of the linked map and then iterating getting the
/// value and linkage stored at the key until the found linkage has no next key.
///
/// # Warning
///
/// If the keys are not trusted (e.g. can be set by a user), a cryptographic `hasher` such as
/// `blake2_256` must be used. Otherwise, other values in storage can be compromised.
pub trait KeyFormat {
	/// Hasher. Used for generating final key and final head key.
	type Hasher: StorageHasher;

	/// Module prefix. Used for generating final key.
	fn module_prefix() -> &'static [u8];

	/// Storage prefix. Used for generating final key.
	fn storage_prefix() -> &'static [u8];

	/// Storage prefix. Used for generating final head key.
	fn head_prefix() -> &'static [u8];

	/// Generate the full key used in top storage.
	fn storage_linked_map_final_key<K>(key: &K) -> Vec<u8>
	where
		K: Encode,
	{
		let module_prefix_hashed = Twox128::hash(Self::module_prefix());
		let storage_prefix_hashed = Twox128::hash(Self::storage_prefix());
		let key_hashed = key.using_encoded(Self::Hasher::hash);

		let mut final_key = Vec::with_capacity(
			module_prefix_hashed.len() + storage_prefix_hashed.len() + key_hashed.as_ref().len()
		);

		final_key.extend_from_slice(&module_prefix_hashed[..]);
		final_key.extend_from_slice(&storage_prefix_hashed[..]);
		final_key.extend_from_slice(key_hashed.as_ref());

		final_key
	}

	/// Generate the full key used in top storage to store the head of the linked map.
	fn storage_linked_map_final_head_key() -> Vec<u8> {
		[
			Twox128::hash(Self::module_prefix()),
			Twox128::hash(Self::head_prefix()),
		].concat()
	}
}

/// Linkage data of an element (it's successor and predecessor)
#[derive(Encode, Decode)]
pub struct Linkage<Key> {
	/// Previous element key in storage (None for the first element)
	pub previous: Option<Key>,
	/// Next element key in storage (None for the last element)
	pub next: Option<Key>,
}

impl<Key> Default for Linkage<Key> {
	fn default() -> Self {
		Self {
			previous: None,
			next: None,
		}
	}
}

// Encode like a linkage.
#[derive(Encode)]
struct EncodeLikeLinkage<PKey: EncodeLike<Key>, NKey: EncodeLike<Key>, Key: Encode> {
	// Previous element key in storage (None for the first element)
	previous: Option<PKey>,
	// Next element key in storage (None for the last element)
	next: Option<NKey>,
	// The key of the linkage this type encode to
	phantom: core::marker::PhantomData<Key>,
}

/// A key-value pair iterator for enumerable map.
pub struct Enumerator<K, V, F> {
	next: Option<K>,
	_phantom: PhantomData<(V, F)>,
}

impl<K, V, F> Enumerator<K, V, F> {
	/// Create an explicit enumerator for testing.
	#[cfg(test)]
	pub fn from_head(head: K) -> Self {
		Enumerator {
			next: Some(head),
			_phantom: Default::default(),
		}
	}
}

impl<K, V, F> Iterator for Enumerator<K, V, F>
where
	K: FullCodec,
	V: FullCodec,
	F: KeyFormat,
{
	type Item = (K, V);

	fn next(&mut self) -> Option<Self::Item> {
		let next = self.next.take()?;

		let (val, linkage): (V, Linkage<K>) = {
			let next_full_key = F::storage_linked_map_final_key(&next);
			match read_with_linkage::<K, V>(next_full_key.as_ref()) {
				Some(value) => value,
				None => {
					// TODO #3700: error should be handleable.
					runtime_print!(
						"ERROR: Corrupted state: linked map {:?}{:?}: \
						next value doesn't exist at {:?}",
						F::module_prefix(), F::storage_prefix(), next_full_key,
					);
					return None
				}
			}
		};

		self.next = linkage.next;
		Some((next, val))
	}
}

/// Update linkage when this element is removed.
///
/// Takes care of updating previous and next elements points
/// as well as updates head if the element is first or last.
fn remove_linkage<K, V, F>(linkage: Linkage<K>)
where
	K: FullCodec,
	V: FullCodec,
	F: KeyFormat,
{
	let next_key = linkage.next.as_ref().map(|k| F::storage_linked_map_final_key(k));
	let prev_key = linkage.previous.as_ref().map(|k| F::storage_linked_map_final_key(k));

	if let Some(prev_key) = prev_key {
		// Retrieve previous element and update `next`
		if let Some(mut res) = read_with_linkage::<K, V>(prev_key.as_ref()) {
			res.1.next = linkage.next;
			unhashed::put(prev_key.as_ref(), &res);
		} else {
			// TODO #3700: error should be handleable.
			runtime_print!(
				"ERROR: Corrupted state: linked map {:?}{:?}: \
				previous value doesn't exist at {:?}",
				F::module_prefix(), F::storage_prefix(), prev_key,
			);
		}
	} else {
		// we were first so let's update the head
		write_head::<&K, K, F>(linkage.next.as_ref());
	}
	if let Some(next_key) = next_key {
		// Update previous of next element
		if let Some(mut res) = read_with_linkage::<K, V>(next_key.as_ref()) {
			res.1.previous = linkage.previous;
			unhashed::put(next_key.as_ref(), &res);
		} else {
			// TODO #3700: error should be handleable.
			runtime_print!(
				"ERROR: Corrupted state: linked map {:?}{:?}: \
				next value doesn't exist at {:?}",
				F::module_prefix(), F::storage_prefix(), next_key,
			);
		}
	}
}

/// Read the contained data and its linkage.
pub(super) fn read_with_linkage<K, V>(key: &[u8]) -> Option<(V, Linkage<K>)>
where
	K: Decode,
	V: Decode,
{
	unhashed::get(key)
}

/// Generate linkage for newly inserted element.
///
/// Takes care of updating head and previous head's pointer.
pub(super) fn new_head_linkage<KeyArg, K, V, F>(key: KeyArg) -> Linkage<K>
where
	KeyArg: EncodeLike<K>,
	K: FullCodec,
	V: FullCodec,
	F: KeyFormat,
{
	if let Some(head) = read_head::<K, F>() {
		// update previous head predecessor
		{
			let head_key = F::storage_linked_map_final_key(&head);
			if let Some((data, linkage)) = read_with_linkage::<K, V>(head_key.as_ref()) {
				let new_linkage = EncodeLikeLinkage::<_, _, K> {
					previous: Some(Ref::from(&key)),
					next: linkage.next.as_ref(),
					phantom: Default::default(),
				};
				unhashed::put(head_key.as_ref(), &(data, new_linkage));
			} else {
				// TODO #3700: error should be handleable.
				runtime_print!(
					"ERROR: Corrupted state: linked map {:?}{:?}: \
					head value doesn't exist at {:?}",
					F::module_prefix(), F::storage_prefix(), head_key,
				);
				// Thus we consider we are first - update the head and produce empty linkage

				write_head::<_, _, F>(Some(key));
				return Linkage::default();
			}
		}
		// update to current head
		write_head::<_, _, F>(Some(key));
		// return linkage with pointer to previous head
		let mut linkage = Linkage::default();
		linkage.next = Some(head);
		linkage
	} else {
		// we are first - update the head and produce empty linkage
		write_head::<_, _, F>(Some(key));
		Linkage::default()
	}
}

/// Read current head pointer.
pub(crate) fn read_head<K, F>() -> Option<K>
where
	K: Decode,
	F: KeyFormat,
{
	unhashed::get(F::storage_linked_map_final_head_key().as_ref())
}

/// Overwrite current head pointer.
///
/// If `None` is given head is removed from storage.
pub(super) fn write_head<KeyArg, K, F>(head: Option<KeyArg>)
where
	KeyArg: EncodeLike<K>,
	K: FullCodec,
	F: KeyFormat,
{
	match head.as_ref() {
		Some(head) => unhashed::put(F::storage_linked_map_final_head_key().as_ref(), head),
		None => unhashed::kill(F::storage_linked_map_final_head_key().as_ref()),
	}
}

impl<K, V, G> storage::StorageLinkedMap<K, V> for G
where
	K: FullCodec,
	V: FullCodec,
	G: StorageLinkedMap<K, V>,
{
	type Query = G::Query;

	type Enumerator = Enumerator<K, V, G::KeyFormat>;

	fn exists<KeyArg: EncodeLike<K>>(key: KeyArg) -> bool {
		unhashed::exists(Self::storage_linked_map_final_key(key).as_ref())
	}

	fn get<KeyArg: EncodeLike<K>>(key: KeyArg) -> Self::Query {
		let val = unhashed::get(Self::storage_linked_map_final_key(key).as_ref());
		G::from_optional_value_to_query(val)
	}

	fn swap<KeyArg1: EncodeLike<K>, KeyArg2: EncodeLike<K>>(key1: KeyArg1, key2: KeyArg2) {
		let final_key1 = Self::storage_linked_map_final_key(Ref::from(&key1));
		let final_key2 = Self::storage_linked_map_final_key(Ref::from(&key2));
		let full_value_1 = read_with_linkage::<K, V>(final_key1.as_ref());
		let full_value_2 = read_with_linkage::<K, V>(final_key2.as_ref());

		match (full_value_1, full_value_2) {
			// Just keep linkage in order and only swap values.
			(Some((value1, linkage1)), Some((value2, linkage2))) => {
				unhashed::put(final_key1.as_ref(), &(value2, linkage1));
				unhashed::put(final_key2.as_ref(), &(value1, linkage2));
			}
			// Remove key and insert the new one.
			(Some((value, _linkage)), None) => {
				Self::remove(key1);
				let linkage = new_head_linkage::<_, _, V, G::KeyFormat>(key2);
				unhashed::put(final_key2.as_ref(), &(value, linkage));
			}
			// Remove key and insert the new one.
			(None, Some((value, _linkage))) => {
				Self::remove(key2);
				let linkage = new_head_linkage::<_, _, V, G::KeyFormat>(key1);
				unhashed::put(final_key1.as_ref(), &(value, linkage));
			}
			// No-op.
			(None, None) => (),
		}
	}

	fn insert<KeyArg: EncodeLike<K>, ValArg: EncodeLike<V>>(key: KeyArg, val: ValArg) {
		let final_key = Self::storage_linked_map_final_key(Ref::from(&key));
		let linkage = match read_with_linkage::<_, V>(final_key.as_ref()) {
			// overwrite but reuse existing linkage
			Some((_data, linkage)) => linkage,
			// create new linkage
			None => new_head_linkage::<_, _, V, G::KeyFormat>(key),
		};
		unhashed::put(final_key.as_ref(), &(val, linkage))
	}

	fn remove<KeyArg: EncodeLike<K>>(key: KeyArg) {
		G::take(key);
	}

	fn mutate<KeyArg: EncodeLike<K>, R, F: FnOnce(&mut Self::Query) -> R>(key: KeyArg, f: F) -> R {
		let final_key = Self::storage_linked_map_final_key(Ref::from(&key));

		let (mut val, _linkage) = read_with_linkage::<K, V>(final_key.as_ref())
			.map(|(data, linkage)| (G::from_optional_value_to_query(Some(data)), Some(linkage)))
			.unwrap_or_else(|| (G::from_optional_value_to_query(None), None));

		let ret = f(&mut val);
		match G::from_query_to_optional_value(val) {
			Some(ref val) => G::insert(key, val),
			None => G::remove(key),
		}
		ret
	}

	fn take<KeyArg: EncodeLike<K>>(key: KeyArg) -> Self::Query {
		let final_key = Self::storage_linked_map_final_key(key);

		let full_value: Option<(V, Linkage<K>)> = unhashed::take(final_key.as_ref());

		let value = full_value.map(|(data, linkage)| {
			remove_linkage::<K, V, G::KeyFormat>(linkage);
			data
		});

		G::from_optional_value_to_query(value)
	}

	fn enumerate() -> Self::Enumerator {
		Enumerator::<_, _, G::KeyFormat> {
			next: read_head::<_, G::KeyFormat>(),
			_phantom: Default::default(),
		}
	}

	fn head() -> Option<K> {
		read_head::<_, G::KeyFormat>()
	}

	fn decode_len<KeyArg: EncodeLike<K>>(key: KeyArg) -> Result<usize, &'static str>
		where V: codec::DecodeLength + Len
	{
		let key = Self::storage_linked_map_final_key(key);
		if let Some(v) = unhashed::get_raw(key.as_ref()) {
			<V as codec::DecodeLength>::len(&v).map_err(|e| e.what())
		} else {
			let len = G::from_query_to_optional_value(G::from_optional_value_to_query(None))
				.map(|v| v.len())
				.unwrap_or(0);

			Ok(len)
		}
	}

	fn translate<K2, V2, TK, TV>(translate_key: TK, translate_val: TV) -> Result<(), Option<K2>>
		where K2: FullCodec + Clone, V2: Decode, TK: Fn(K2) -> K, TV: Fn(V2) -> V
	{
		let head_key = read_head::<K2, G::KeyFormat>().ok_or(None)?;

		let mut last_key = None;
		let mut current_key = head_key.clone();

		write_head::<&K, K, G::KeyFormat>(Some(&translate_key(head_key)));

		let translate_linkage = |old: Linkage<K2>| -> Linkage<K> {
			Linkage {
				previous: old.previous.map(&translate_key),
				next: old.next.map(&translate_key),
			}
		};

		loop {
			let old_raw_key = G::KeyFormat::storage_linked_map_final_key(&current_key);
			let x = unhashed::take(old_raw_key.as_ref());
			let (val, linkage): (V2, Linkage<K2>) = match x {
				Some(v) => v,
				None => {
					// we failed to read value and linkage. Update the last key's linkage
					// to end the map early, since it's impossible to iterate further.
					if let Some(last_key) = last_key {
						let last_raw_key = G::storage_linked_map_final_key(&last_key);
						if let Some((val, mut linkage))
							= read_with_linkage::<K, V>(last_raw_key.as_ref())
						{
							// defensive: should always happen, since it was just written
							// in the last iteration of the loop.
							linkage.next = None;
							unhashed::put(last_raw_key.as_ref(), &(&val, &linkage));
						}
					}

					return Err(Some(current_key));
				}
			};
			let next = linkage.next.clone();

			let val = translate_val(val);
			let linkage = translate_linkage(linkage);

			// and write in the value and linkage under the new key.
			let new_key = translate_key(current_key.clone());
			let new_raw_key = G::storage_linked_map_final_key(&new_key);
			unhashed::put(new_raw_key.as_ref(), &(&val, &linkage));

			match next {
				None => break,
				Some(next) => {
					last_key = Some(new_key);
					current_key = next
				},
			}
		}

		Ok(())
	}
}
