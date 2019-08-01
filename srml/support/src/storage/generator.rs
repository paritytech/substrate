use crate::rstd::borrow::Borrow;
use crate::rstd::boxed::Box;
use crate::rstd::marker::PhantomData;
use codec::{Codec, Encode, Decode, EncodeAppend};
use runtime_io::{twox_64, twox_128, blake2_128, twox_256, blake2_256};
use super::unhashed;
use super::child;

// TODO TODO: just maybe reduce the scope of the PR because of storage_item macro:
// * remove generator
// * move linkedmap to its own trait
// * storage items impls directly main trait
// * decl_storage use new generators
//
// finally this is fine just do storage_items impls directly into main trait.
// also we can still used hashed storage here instead of using only unhashed. but OK

/// TODO TODO: doc
pub trait StorageHasher: 'static {
	type Output: AsRef<[u8]>;
	fn hash(x: &[u8]) -> Self::Output;
}

/// Hash storage keys with `concat(twox64(key), key)`
pub struct Twox64Concat;
impl StorageHasher for Twox64Concat {
	type Output = Vec<u8>;
	fn hash(x: &[u8]) -> Vec<u8> {
		twox_64(x)
			.into_iter()
			.chain(x.into_iter())
			.cloned()
			.collect::<Vec<_>>()
	}
}

#[test]
fn test_twox_64_concat() {
	let r = Twox64Concat::hash(b"foo");
	assert_eq!(r.split_at(8), (&twox_128(b"foo")[..8], &b"foo"[..]))
}

/// Hash storage keys with blake2 128
pub struct Blake2_128;
impl StorageHasher for Blake2_128 {
	type Output = [u8; 16];
	fn hash(x: &[u8]) -> [u8; 16] {
		blake2_128(x)
	}
}

/// Hash storage keys with blake2 256
pub struct Blake2_256;
impl StorageHasher for Blake2_256 {
	type Output = [u8; 32];
	fn hash(x: &[u8]) -> [u8; 32] {
		blake2_256(x)
	}
}

/// Hash storage keys with twox 128
pub struct Twox128;
impl StorageHasher for Twox128 {
	type Output = [u8; 16];
	fn hash(x: &[u8]) -> [u8; 16] {
		twox_128(x)
	}
}

/// Hash storage keys with twox 256
pub struct Twox256;
impl StorageHasher for Twox256 {
	type Output = [u8; 32];
	fn hash(x: &[u8]) -> [u8; 32] {
		twox_256(x)
	}
}

pub trait StorageValue<T: Codec> {
	/// The type that get/take returns.
	type Query;

	fn key() -> &'static [u8];

	fn from_optional_value_to_query(v: Option<T>) -> Self::Query;

	fn from_query_to_optional_value(v: Self::Query) -> Option<T>;
}

fn storage_value_final_key<T: Codec, S: StorageValue<T>>() -> impl AsRef<[u8]> {
	Twox256::hash(S::key())
}

impl<T: Codec, G: StorageValue<T>> super::StorageValue<T> for G {
	type Query = G::Query;

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
		).ok_or_else(|| "Could not append given item")?;
		unhashed::put_raw(key.as_ref(), &new_val);
		Ok(())
	}
}

pub trait StorageMap<K: Codec, V: Codec> {
	/// The type that get/take returns.
	type Query;

	type Hasher: StorageHasher;

	fn prefix() -> &'static [u8];

	// Could we change this just asking for the default value ?
	fn from_optional_value_to_query(v: Option<V>) -> Self::Query;

	fn from_query_to_optional_value(v: Self::Query) -> Option<V>;
}

fn storage_map_final_key<KeyArg, K, V, G>(key: KeyArg) -> impl AsRef<[u8]>
where
	KeyArg: Borrow<K>,
	K: Codec,
	V: Codec,
	G: StorageMap<K, V>
{
	let mut final_key = G::prefix().to_vec();
	key.borrow().encode_to(&mut final_key);
	G::Hasher::hash(&final_key)
}

impl<K: Codec, V: Codec, G: StorageMap<K, V>> super::StorageMap<K, V> for G {
	type Query = G::Query;

	fn exists<KeyArg: Borrow<K>>(key: KeyArg) -> bool {
		unhashed::exists(storage_map_final_key::<_, _, _, G>(key).as_ref())
	}

	fn get<KeyArg: Borrow<K>>(key: KeyArg) -> Self::Query {
		G::from_optional_value_to_query(unhashed::get(storage_map_final_key::<_, _, _, G>(key).as_ref()))
	}

	fn insert<KeyArg: Borrow<K>, ValArg: Borrow<V>>(key: KeyArg, val: ValArg) {
		unhashed::put(storage_map_final_key::<_, _, _, G>(key).as_ref(), &val.borrow())
	}

	fn insert_ref<KeyArg: Borrow<K>, ValArg: ?Sized + Encode>(key: KeyArg, val: &ValArg)
		where V: AsRef<ValArg>
	{
		val.using_encoded(|b| unhashed::put_raw(storage_map_final_key::<_, _, _, G>(key).as_ref(), b))
	}

	fn remove<KeyArg: Borrow<K>>(key: KeyArg) {
		unhashed::kill(storage_map_final_key::<_, _, _, G>(key).as_ref())
	}

	fn mutate<KeyArg: Borrow<K>, R, F: FnOnce(&mut Self::Query) -> R>(key: KeyArg, f: F) -> R {
		// TODO TODO: avoid computing key everytime
		let mut val = G::get(key.borrow());

		let ret = f(&mut val);
		match G::from_query_to_optional_value(val) {
			Some(ref val) => G::insert(key, val),
			None => G::remove(key),
		}
		ret
	}

	fn take<KeyArg: Borrow<K>>(key: KeyArg) -> Self::Query {
		let key = storage_map_final_key::<_, _, _, G>(key);
		let value = unhashed::get(key.as_ref());
		if value.is_some() {
			unhashed::kill(key.as_ref())
		}
		G::from_optional_value_to_query(value)
	}

	fn append<KeyArg: Borrow<K>, I: Encode>(key: KeyArg, items: &[I]) -> Result<(), &'static str>
		where V: EncodeAppend<Item=I>
	{
		let key = storage_map_final_key::<_, _, _, G>(key);
		let encoded_value = unhashed::get_raw(key.as_ref())
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
		unhashed::put_raw(key.as_ref(), &new_val);
		Ok(())
	}
}

pub trait StorageLinkedMap<K: Codec, V: Codec> {
	/// The type that get/take returns.
	type Query;

	type Hasher: StorageHasher;

	fn prefix() -> &'static [u8];

	fn final_head_key() -> &'static [u8];

	fn from_optional_value_to_query(v: Option<V>) -> Self::Query;

	fn from_query_to_optional_value(v: Self::Query) -> Option<V>;
}

fn storage_linked_map_final_key<KeyArg, K, V, G>(key: KeyArg) -> impl AsRef<[u8]>
where
	KeyArg: Borrow<K>,
	K: Codec,
	V: Codec,
	G: StorageLinkedMap<K, V>
{
	let mut final_key = G::prefix().to_vec();
	key.borrow().encode_to(&mut final_key);
	G::Hasher::hash(&final_key)
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

/// A key-value pair iterator for enumerable map.
struct Enumerator<K: Codec, V: Codec, G: StorageLinkedMap<K, V>> {
	next: Option<K>,
	_phantom: PhantomData<(G, V)>,
}

impl<K: Codec, V: Codec, G: StorageLinkedMap<K, V>> Iterator for Enumerator<K, V, G> {
	type Item = (K, V);

	fn next(&mut self) -> Option<Self::Item> {
		let next = self.next.take()?;
		let (val, linkage): (V, Linkage<K>) = {
			let next_full_key = storage_linked_map_final_key::<_, _, _, G>(&next);
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
fn remove_linkage<K: Codec, V: Codec, G: StorageLinkedMap<K, V>>(linkage: Linkage<K>) {
	let next_key = linkage.next.as_ref()
		.map(storage_linked_map_final_key::<_, _, _, G>)
		.map(|x| x.as_ref().to_vec());
	let prev_key = linkage.previous.as_ref()
		.map(storage_linked_map_final_key::<_, _, _, G>)
		.map(|x| x.as_ref().to_vec());

	if let Some(prev_key) = prev_key {
		// Retrieve previous element and update `next`
		let mut res = read_with_linkage::<K, V, G>(prev_key.as_ref())
			.expect("Linkage is updated in case entry is removed; it always points to existing keys; qed");
		res.1.next = linkage.next;
		unhashed::put(prev_key.as_ref(), &res);
	} else {
		// we were first so let's update the head
		write_head::<K, V, G>(linkage.next.as_ref());
	}
	if let Some(next_key) = next_key {
		// Update previous of next element
		let mut res = read_with_linkage::<K, V, G>(next_key.as_ref())
			.expect("Linkage is updated in case entry is removed; it always points to existing keys; qed");
		res.1.previous = linkage.previous;
		unhashed::put(next_key.as_ref(), &res);
	}
}

/// Read the contained data and it's linkage.
fn read_with_linkage<K, V, G>(key: &[u8]) -> Option<(V, Linkage<K>)>
where
	K: Codec,
	V: Codec,
	G: StorageLinkedMap<K, V>
{
	unhashed::get(key)
}

/// Generate linkage for newly inserted element.
///
/// Takes care of updating head and previous head's pointer.
fn new_head_linkage<K, V, G>(key: &K) -> Linkage<K>
where
	K: Codec,
	V: Codec,
	G: StorageLinkedMap<K, V>
{
	if let Some(head) = read_head::<K, V, G>() {
		// update previous head predecessor
		{
			let head_key = storage_linked_map_final_key::<_, _, _, G>(&head);
			let (data, linkage) = read_with_linkage::<K, V, G>(head_key.as_ref()).expect(r#"
								head is set when first element is inserted and unset when last element is removed;
								if head is Some then it points to existing key; qed
							"#);
			unhashed::put(head_key.as_ref(), &(data, Linkage {
				next: linkage.next.as_ref(),
				previous: Some(key),
			}));
		}
		// update to current head
		write_head::<K, V, G>(Some(key));
		// return linkage with pointer to previous head
		let mut linkage = Linkage::default();
		linkage.next = Some(head);
		linkage
	} else {
		// we are first - update the head and produce empty linkage
		write_head::<K, V, G>(Some(key));
		Linkage::default()
	}
}

/// Read current head pointer.
fn read_head<K, V, G>() -> Option<K>
where
	K: Codec,
	V: Codec,
	G: StorageLinkedMap<K, V>
{
	unhashed::get(G::final_head_key())
}

/// Overwrite current head pointer.
///
/// If `None` is given head is removed from storage.
fn write_head<K, V, G>(head: Option<&K>)
where
	K: Codec,
	V: Codec,
	G: StorageLinkedMap<K, V>
{
	match head {
		Some(head) => unhashed::put(G::final_head_key(), head),
		None => unhashed::kill(G::final_head_key()),
	}
}

impl<K: Codec, V: Codec, G: StorageLinkedMap<K, V>> super::StorageLinkedMap<K, V> for G {
	type Query = G::Query;

	fn exists<KeyArg: Borrow<K>>(key: KeyArg) -> bool {
		unhashed::exists(storage_linked_map_final_key::<_, _, _, G>(key).as_ref())
	}

	fn get<KeyArg: Borrow<K>>(key: KeyArg) -> Self::Query {
		G::from_optional_value_to_query(unhashed::get(storage_linked_map_final_key::<_, _, _, G>(key).as_ref()))
	}

	fn insert<KeyArg: Borrow<K>, ValArg: Borrow<V>>(key: KeyArg, val: ValArg) {
		let final_key = storage_linked_map_final_key::<_, _, _, G>(key.borrow());
		let linkage = match read_with_linkage::<K, V, G>(final_key.as_ref()) {
			// overwrite but reuse existing linkage
			Some((_data, linkage)) => linkage,
			// create new linkage
			None => new_head_linkage::<K, V, G>(key.borrow()),
		};
		unhashed::put(final_key.as_ref(), &(val.borrow(), linkage))
	}

	fn insert_ref<KeyArg: Borrow<K>, ValArg: ?Sized + Encode>(key: KeyArg, val: &ValArg) where V: AsRef<ValArg> {
		let final_key = storage_linked_map_final_key::<_, _, _, G>(key.borrow());
		let linkage = match read_with_linkage::<K, V, G>(final_key.as_ref()) {
			// overwrite but reuse existing linkage
			Some((_data, linkage)) => linkage,
			// create new linkage
			None => new_head_linkage::<K, V, G>(key.borrow()),
		};
		unhashed::put(final_key.as_ref(), &(&val, &linkage))
	}

	fn remove<KeyArg: Borrow<K>>(key: KeyArg) {
		G::take(key);
	}

	fn mutate<KeyArg: Borrow<K>, R, F: FnOnce(&mut Self::Query) -> R>(key: KeyArg, f: F) -> R {
		let final_key = storage_linked_map_final_key::<_, _, _, G>(key.borrow());
		// TODO TODO: rewrite those 3 lines a bit
		let (mut val, _linkage) = read_with_linkage::<K, V, G>(final_key.as_ref())
			.map(|(data, linkage)| (G::from_optional_value_to_query(Some(data)), Some(linkage)))
			.unwrap_or_else(|| (G::from_optional_value_to_query(None), None));

		let ret = f(&mut val);
		match G::from_query_to_optional_value(val) {
			// TODO TODO: This could be optimised
			Some(ref val) => G::insert(key.borrow(), val),
			None => G::remove(key.borrow()),
		}
		ret
	}

	fn take<KeyArg: Borrow<K>>(key: KeyArg) -> Self::Query {
		let final_key = storage_linked_map_final_key::<_, _, _, G>(key);

		let full_value: Option<(V, Linkage<K>)> = unhashed::get(final_key.as_ref());

		let value = match full_value {
			Some((data, linkage)) => {
				unhashed::kill(final_key.as_ref());
				remove_linkage::<K, V, G>(linkage);
				Some(data)
			},
			None => None,
		};

		G::from_optional_value_to_query(value)
	}

	// TODO TODO: we could implemented append by using a fixed size linkage.

	fn enumerate() -> Box<dyn Iterator<Item = (K, V)>> where K: 'static, V: 'static, Self: 'static {
		Box::new(Enumerator::<K, V, G> {
			next: read_head::<K, V, G>(),
			_phantom: Default::default(),
		})
	}
}

pub trait StorageDoubleMap<K1: Encode, K2: Encode, V: Codec> {
	/// The type that get/take returns.
	type Query;

	type Hasher: StorageHasher;

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
	G::Hasher::hash(&final_key1)
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
	k2.encode_to(&mut final_key);
	final_key
}

impl<K1: Encode, K2: Encode, V: Codec, G: StorageDoubleMap<K1, K2, V>> super::StorageDoubleMap<K1, K2, V> for G {
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
