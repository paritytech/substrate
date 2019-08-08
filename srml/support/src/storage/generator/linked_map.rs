use codec::{Codec, Encode, Decode};
use crate::{
	storage::{self, unhashed, hashed::StorageHasher},
	rstd::{
		borrow::Borrow,
		boxed::Box,
		marker::PhantomData,
	}
};

// TODO TODO: look again with https://github.com/paritytech/substrate/pull/3323#event-2540726461

pub trait StorageLinkedMap<K: Codec, V: Codec> {
	/// The type that get/take returns.
	type Query;

	type Hasher: StorageHasher;

	fn prefix() -> &'static [u8];

	fn final_head_key() -> &'static [u8];

	fn from_optional_value_to_query(v: Option<V>) -> Self::Query;

	fn from_query_to_optional_value(v: Self::Query) -> Option<V>;

	fn storage_linked_map_final_key<KeyArg>(key: KeyArg) -> <Self::Hasher as StorageHasher>::Output
	where
		KeyArg: Borrow<K>,
	{
		let mut final_key = Self::prefix().to_vec();
		key.borrow().encode_to(&mut final_key);
		Self::Hasher::hash(&final_key)
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
fn remove_linkage<K: Codec, V: Codec, G: StorageLinkedMap<K, V>>(linkage: Linkage<K>) {
	let next_key = linkage.next.as_ref()
		.map(G::storage_linked_map_final_key)
		.map(|x| x.as_ref().to_vec());
	let prev_key = linkage.previous.as_ref()
		.map(G::storage_linked_map_final_key)
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
			let head_key = G::storage_linked_map_final_key(&head);
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

impl<K: Codec, V: Codec, G: StorageLinkedMap<K, V>> storage::StorageLinkedMap<K, V> for G {
	type Query = G::Query;

	fn exists<KeyArg: Borrow<K>>(key: KeyArg) -> bool {
		unhashed::exists(Self::storage_linked_map_final_key(key).as_ref())
	}

	fn get<KeyArg: Borrow<K>>(key: KeyArg) -> Self::Query {
		G::from_optional_value_to_query(unhashed::get(Self::storage_linked_map_final_key(key).as_ref()))
	}

	fn insert<KeyArg: Borrow<K>, ValArg: Borrow<V>>(key: KeyArg, val: ValArg) {
		let final_key = Self::storage_linked_map_final_key(key.borrow());
		let linkage = match read_with_linkage::<K, V, G>(final_key.as_ref()) {
			// overwrite but reuse existing linkage
			Some((_data, linkage)) => linkage,
			// create new linkage
			None => new_head_linkage::<K, V, G>(key.borrow()),
		};
		unhashed::put(final_key.as_ref(), &(val.borrow(), linkage))
	}

	fn insert_ref<KeyArg: Borrow<K>, ValArg: ?Sized + Encode>(key: KeyArg, val: &ValArg) where V: AsRef<ValArg> {
		let final_key = Self::storage_linked_map_final_key(key.borrow());
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
		let final_key = Self::storage_linked_map_final_key(key.borrow());
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
		let final_key = Self::storage_linked_map_final_key(key);

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

	fn enumerate() -> Box<dyn Iterator<Item = (K, V)>> where K: 'static, V: 'static, Self: 'static {
		Box::new(Enumerator::<K, V, G> {
			next: read_head::<K, V, G>(),
			_phantom: Default::default(),
		})
	}

	fn head() -> Option<K> {
		read_head::<K, V, G>()
	}
}
