// Copyright 2019 Parity Technologies (UK) Ltd.
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
use crate::{storage::{self, unhashed}, hash::StorageHasher, traits::Len};
use rstd::marker::PhantomData;

/// Generator for `StorageLinkedMap` used by `decl_storage`.
///
/// # Mapping of keys to a storage path
///
/// The key for the head of the map is stored at one fixed path:
/// ```nocompile
/// Hasher(head_key)
/// ```
///
/// For each key, the value stored under that key is appended with a
/// [`Linkage`](struct.Linkage.html) (which hold previous and next key) at the path:
/// ```nocompile
/// Hasher(prefix ++ key)
/// ```
///
/// Enumeration is done by getting the head of the linked map and then iterating getting the
/// value and linkage stored at the key until the found linkage has no next key.
///
/// # Warning
///
/// If the keys are not trusted (e.g. can be set by a user), a cryptographic `hasher` such as
/// `blake2_256` must be used. Otherwise, other values in storage can be compromised.
pub trait StorageLinkedMap<K: FullCodec, V: FullCodec> {
	/// The type that get/take returns.
	type Query;

	/// Hasher used to insert into storage.
	type Hasher: StorageHasher;

	/// Prefix used to prepend each key.
	fn prefix() -> &'static [u8];

	/// Key used to store linked map head.
	fn head_key() -> &'static [u8];

	/// Convert an optionnal value retrieved from storage to the type queried.
	fn from_optional_value_to_query(v: Option<V>) -> Self::Query;

	/// Convert a query to an optionnal value into storage.
	fn from_query_to_optional_value(v: Self::Query) -> Option<V>;

	/// Generate the full key used in top storage.
	fn storage_linked_map_final_key<KeyArg>(key: KeyArg) -> <Self::Hasher as StorageHasher>::Output
	where
		KeyArg: EncodeLike<K>,
	{
		let mut final_key = Self::prefix().to_vec();
		key.encode_to(&mut final_key);
		Self::Hasher::hash(&final_key)
	}

	/// Generate the hashed key for head
	fn storage_linked_map_final_head_key() -> <Self::Hasher as StorageHasher>::Output {
		Self::Hasher::hash(Self::head_key())
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
pub struct Enumerator<K: FullCodec, V: FullCodec, G: StorageLinkedMap<K, V>> {
	next: Option<K>,
	_phantom: PhantomData<(G, V)>,
}

impl<K, V, G> Iterator for Enumerator<K, V, G>
where
	K: FullCodec,
	V: FullCodec,
	G: StorageLinkedMap<K, V>,
{
	type Item = (K, V);

	fn next(&mut self) -> Option<Self::Item> {
		let next = self.next.take()?;
		let (val, linkage): (V, Linkage<K>) = {
			let next_full_key = G::storage_linked_map_final_key(&next);
			unhashed::get(next_full_key.as_ref())
				.expect("previous/next only contain existing entires;
						we enumerate using next; entry exists; qed")
		};

		self.next = linkage.next;
		Some((next, val))
	}
}

/// Update linkage when this element is removed.
///
/// Takes care of updating previous and next elements points
/// as well as updates head if the element is first or last.
fn remove_linkage<K, V, G>(linkage: Linkage<K>)
where
	K: FullCodec,
	V: FullCodec,
	G: StorageLinkedMap<K, V>,
{
	let next_key = linkage.next.as_ref()
		.map(G::storage_linked_map_final_key)
		.map(|x| x.as_ref().to_vec());
	let prev_key = linkage.previous.as_ref()
		.map(G::storage_linked_map_final_key)
		.map(|x| x.as_ref().to_vec());

	if let Some(prev_key) = prev_key {
		// Retrieve previous element and update `next`
		let mut res = read_with_linkage::<_, _, G>(prev_key.as_ref())
			.expect("Linkage is updated in case entry is removed;
					it always points to existing keys; qed");
		res.1.next = linkage.next;
		unhashed::put(prev_key.as_ref(), &res);
	} else {
		// we were first so let's update the head
		write_head::<_, _, _, G>(linkage.next.as_ref());
	}
	if let Some(next_key) = next_key {
		// Update previous of next element
		let mut res = read_with_linkage::<_, _, G>(next_key.as_ref())
			.expect("Linkage is updated in case entry is removed;
					it always points to existing keys; qed");
		res.1.previous = linkage.previous;
		unhashed::put(next_key.as_ref(), &res);
	}
}

/// Read the contained data and it's linkage.
fn read_with_linkage<K, V, G>(key: &[u8]) -> Option<(V, Linkage<K>)>
where
	K: FullCodec,
	V: FullCodec,
	G: StorageLinkedMap<K, V>,
{
	unhashed::get(key)
}

/// Generate linkage for newly inserted element.
///
/// Takes care of updating head and previous head's pointer.
fn new_head_linkage<KeyArg, K, V, G>(key: KeyArg) -> Linkage<K>
where
	KeyArg: EncodeLike<K>,
	K: FullCodec,
	V: FullCodec,
	G: StorageLinkedMap<K, V>,
{
	if let Some(head) = read_head::<_, _, G>() {
		// update previous head predecessor
		{
			let head_key = G::storage_linked_map_final_key(&head);
			let (data, linkage) = read_with_linkage::<_, _, G>(head_key.as_ref())
				.expect("head is set when first element is inserted
						and unset when last element is removed;
						if head is Some then it points to existing key; qed");
			let new_linkage = EncodeLikeLinkage::<_, _, K> {
				previous: Some(Ref::from(&key)),
				next: linkage.next.as_ref(),
				phantom: Default::default(),
			};
			unhashed::put(head_key.as_ref(), &(data, new_linkage));
		}
		// update to current head
		write_head::<_, _, _, G>(Some(key));
		// return linkage with pointer to previous head
		let mut linkage = Linkage::default();
		linkage.next = Some(head);
		linkage
	} else {
		// we are first - update the head and produce empty linkage
		write_head::<_, _, _, G>(Some(key));
		Linkage::default()
	}
}

/// Read current head pointer.
fn read_head<K, V, G>() -> Option<K>
where
	K: FullCodec,
	V: FullCodec,
	G: StorageLinkedMap<K, V>,
{
	unhashed::get(G::storage_linked_map_final_head_key().as_ref())
}

/// Overwrite current head pointer.
///
/// If `None` is given head is removed from storage.
fn write_head<KeyArg, K, V, G>(head: Option<KeyArg>)
where
	KeyArg: EncodeLike<K>,
	K: FullCodec,
	V: FullCodec,
	G: StorageLinkedMap<K, V>,
{
	match head.as_ref() {
		Some(head) => unhashed::put(G::storage_linked_map_final_head_key().as_ref(), head),
		None => unhashed::kill(G::storage_linked_map_final_head_key().as_ref()),
	}
}

impl<K, V, G> storage::StorageLinkedMap<K, V> for G
where
	K: FullCodec,
	V: FullCodec,
	G: StorageLinkedMap<K, V>,
{
	type Query = G::Query;

	type Enumerator = Enumerator<K, V, Self>;

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
		let full_value_1 = read_with_linkage::<_, _, G>(final_key1.as_ref());
		let full_value_2 = read_with_linkage::<_, _, G>(final_key2.as_ref());

		match (full_value_1, full_value_2) {
			// Just keep linkage in order and only swap values.
			(Some((value1, linkage1)), Some((value2, linkage2))) => {
				unhashed::put(final_key1.as_ref(), &(value2, linkage1));
				unhashed::put(final_key2.as_ref(), &(value1, linkage2));
			}
			// Remove key and insert the new one.
			(Some((value, _linkage)), None) => {
				Self::remove(key1);
				let linkage = new_head_linkage::<_, _, _, G>(key2);
				unhashed::put(final_key2.as_ref(), &(value, linkage));
			}
			// Remove key and insert the new one.
			(None, Some((value, _linkage))) => {
				Self::remove(key2);
				let linkage = new_head_linkage::<_, _, _, G>(key1);
				unhashed::put(final_key1.as_ref(), &(value, linkage));
			}
			// No-op.
			(None, None) => (),
		}
	}

	fn insert<KeyArg: EncodeLike<K>, ValArg: EncodeLike<V>>(key: KeyArg, val: ValArg) {
		let final_key = Self::storage_linked_map_final_key(Ref::from(&key));
		let linkage = match read_with_linkage::<_, _, G>(final_key.as_ref()) {
			// overwrite but reuse existing linkage
			Some((_data, linkage)) => linkage,
			// create new linkage
			None => new_head_linkage::<_, _, _, G>(key),
		};
		unhashed::put(final_key.as_ref(), &(val, linkage))
	}

	fn remove<KeyArg: EncodeLike<K>>(key: KeyArg) {
		G::take(key);
	}

	fn mutate<KeyArg: EncodeLike<K>, R, F: FnOnce(&mut Self::Query) -> R>(key: KeyArg, f: F) -> R {
		let final_key = Self::storage_linked_map_final_key(Ref::from(&key));

		let (mut val, _linkage) = read_with_linkage::<_, _, G>(final_key.as_ref())
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
			remove_linkage::<_, _, G>(linkage);
			data
		});

		G::from_optional_value_to_query(value)
	}

	fn enumerate() -> Self::Enumerator {
		Enumerator::<_, _, G> {
			next: read_head::<_, _, G>(),
			_phantom: Default::default(),
		}
	}

	fn head() -> Option<K> {
		read_head::<_, _, G>()
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
}
