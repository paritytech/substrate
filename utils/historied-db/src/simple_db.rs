// This file is part of Substrate.

// Copyright (C) 2020-2020 Parity Technologies (UK) Ltd.
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

//! Simple db tools to store non historied information.

use derivative::Derivative;
use sp_std::{collections::btree_map::{BTreeMap, Entry}, marker::PhantomData, vec::Vec};
use sp_std::fmt::Debug;
use sp_std::boxed::Box;

/// Iterator could be associated serializeDB type but dynamic type make things simplier.
pub type SerializeDBIter<'a> = Box<dyn Iterator<Item = (Vec<u8>, Vec<u8>)> + 'a>;

/// simple serialize trait, could be a noop.
pub trait SerializeDB {
	#[inline(always)]
	/// When false, the trait implementation
	/// do not need to actually manage a db
	/// (see `()` implementation).
	/// This could be an associated constant
	/// if it isn't for the dyn pointer requirement.
	fn is_active(&self) -> bool {
		true
	}

	fn write(&mut self, c: &'static [u8], k: &[u8], v: &[u8]);
	fn remove(&mut self, c: &'static [u8], k: &[u8]);
	fn read(&self, c: &'static [u8], k: &[u8]) -> Option<Vec<u8>>;
	fn clear(&mut self, c: &'static [u8]);
	fn iter<'a>(&'a self, c: &'static [u8]) -> SerializeDBIter<'a>;

	fn contains_collection(&self, collection: &'static [u8]) -> bool;
}

pub struct Collection<'a, DB, Instance> {
	db: &'a DB,
	instance: &'a Instance,
}

pub struct CollectionMut<'a, DB, Instance> {
	db: &'a mut DB,
	instance: &'a Instance,
}

impl<'a, DB: SerializeDB, Instance: SerializeInstanceMap> Collection<'a, DB, Instance> {
	pub fn read(&self, k: &[u8]) -> Option<Vec<u8>> {
		self.db.read(Instance::STATIC_COL, k)
	}
	pub fn iter(&self) -> SerializeDBIter<'a> {
		self.db.iter(Instance::STATIC_COL)
	}
}

impl<'a, DB: SerializeDB, Instance: SerializeInstanceMap> CollectionMut<'a, DB, Instance> {
	pub fn write(&mut self, k: &[u8], v: &[u8]) {
		self.db.write(Instance::STATIC_COL, k, v)
	}
	pub fn remove(&mut self, k: &[u8]) {
		self.db.remove(Instance::STATIC_COL, k)
	}
	pub fn read(&self, k: &[u8]) -> Option<Vec<u8>> {
		self.db.read(Instance::STATIC_COL, k)
	}
	pub fn iter<'b>(&'b self) -> SerializeDBIter<'b> {
		self.db.iter(Instance::STATIC_COL)
	}
	pub fn clear(&mut self) {
		self.db.clear(Instance::STATIC_COL)
	}
}

/// Serialize trait, when dynamic collection
/// are allowed.
pub trait DynSerializeDB: SerializeDB {

	/// Create a new collection and return its identifier.
	fn new_dyn_collection(&mut self) -> Vec<u8>;

	fn dyn_write(&mut self, c: &[u8], k: &[u8], v: &[u8]);
	fn dyn_remove(&mut self, c: &[u8], k: &[u8]);
	fn dyn_read(&self, c: &[u8], k: &[u8]) -> Option<Vec<u8>>;
	fn dyn_iter<'a>(&'a self, c: &[u8]) -> SerializeDBIter<'a>;

	fn dyn_contains_collection(collection: &[u8]) -> bool;
}

impl<'a, DB: DynSerializeDB, Instance: DynSerializeInstanceMap> Collection<'a, DB, Instance> {
	pub fn dyn_read(&self, k: &[u8]) -> Option<Vec<u8>> {
		if let Some(c) = self.instance.dyn_collection() {
			self.db.dyn_read(c, k)
		} else {
			self.db.read(Instance::STATIC_COL, k)
		}
	}
	pub fn dyn_iter(&self) -> SerializeDBIter<'a> {
		if let Some(c) = self.instance.dyn_collection() {
			self.db.dyn_iter(c)
		} else {
			self.db.iter(Instance::STATIC_COL)
		}
	}
}

impl<'a, DB: DynSerializeDB, Instance: DynSerializeInstanceMap> CollectionMut<'a, DB, Instance> {
	pub fn dyn_write(&mut self, k: &[u8], v: &[u8]) {
		if let Some(c) = self.instance.dyn_collection() {
			self.db.dyn_write(c, k, v)
		} else {
			self.db.write(Instance::STATIC_COL, k, v)
		}
	}
	pub fn dyn_remove(&mut self, k: &[u8]) {
		if let Some(c) = self.instance.dyn_collection() {
			self.db.dyn_remove(c, k)
		} else {
			self.db.remove(Instance::STATIC_COL, k)
		}
	}
	pub fn dyn_read(&self, k: &[u8]) -> Option<Vec<u8>> {
		if let Some(c) = self.instance.dyn_collection() {
			self.db.dyn_read(c, k)
		} else {
			self.db.read(Instance::STATIC_COL, k)
		}
	}
	pub fn dyn_iter<'b>(&'b self) -> SerializeDBIter<'b> {
		if let Some(c) = self.instance.dyn_collection() {
			self.db.dyn_iter(c)
		} else {
			self.db.iter(Instance::STATIC_COL)
		}
	}
}

/// Info for serialize usage.
///
/// Static collection are using a know identifier that never change.
pub trait SerializeInstanceMap: Default + Clone {
	/// If collection is static this contains its
	/// unique identifier.
	const STATIC_COL: &'static [u8];
}

impl SerializeInstanceMap for () {
	const STATIC_COL: &'static [u8] = &[];
}

/// Dynamic collection can be change.
/// Static and dynamic collection are mutually exclusive, yet instance using both trait should run
/// dynamic first.
pub trait DynSerializeInstanceMap: SerializeInstanceMap {
	/// If collection is dynamic this returns the
	/// current collection unique identifier.
	fn dyn_collection(&self) -> Option<&[u8]>;
}

pub trait SerializeInstanceVariable: SerializeInstanceMap {
	/// Location of the variable in its collection.
	const PATH: &'static [u8];
	/// Indicate if we load lazilly.
	const LAZY: bool;
}

/// Noop implementation.
impl SerializeInstanceVariable for () {
	const PATH: &'static [u8] = &[];
	const LAZY: bool = false;
}

impl SerializeDB for () {
	#[inline(always)]
	fn is_active(&self) -> bool {
		false	
	}
	fn write(&mut self, _c: &[u8], _k: &[u8], _v: &[u8]) { }
	fn clear(&mut self, _c: &[u8]) { }
	fn remove(&mut self, _c: &[u8], _k: &[u8]) { }
	fn read(&self, _c: &[u8], _k: &[u8]) -> Option<Vec<u8>> {
		None
	}
	fn iter<'a>(&'a self, _collection: &[u8]) -> SerializeDBIter<'a> {
		Box::new(sp_std::iter::empty())
	}
	fn contains_collection(&self, _collection: &[u8]) -> bool {
		false
	}
}

/// Serialize db as a boxed dynamic pointer.
pub type SerializeDBDyn = Box<dyn SerializeDB + Send + Sync>;

impl SerializeDB for SerializeDBDyn {
	#[inline(always)]
	fn is_active(&self) -> bool {
		self.as_ref().is_active()	
	}
	fn write(&mut self, c: &'static [u8], k: &[u8], v: &[u8]) {
		self.as_mut().write(c, k, v)	
	}
	fn clear(&mut self, c: &'static [u8]) {
		self.as_mut().clear(c)
	}
	fn remove(&mut self, c: &'static [u8], k: &[u8]) {
		self.as_mut().remove(c, k)
	}
	fn read(&self, c: &'static [u8], k: &[u8]) -> Option<Vec<u8>> {
		self.as_ref().read(c, k)
	}
	fn iter<'a>(&'a self, c: &'static [u8]) -> SerializeDBIter<'a> {
		self.as_ref().iter(c)
	}
	fn contains_collection(&self, c: &'static [u8]) -> bool {
		self.as_ref().contains_collection(c)
	}
}

use codec::{Codec, Encode};

#[derive(Derivative)]
#[derivative(Clone(bound="K: Clone, V: Clone, I: Clone"))]
#[derivative(Debug(bound="K: Debug, V: Debug"))]
#[cfg_attr(test, derivative(PartialEq(bound="K: PartialEq, V: PartialEq")))]
/// Lazy loading serialized map with cache.
/// Updates happens without delay.
pub struct SerializeMap<K: Ord, V, S, I> {
	inner: BTreeMap<K, Option<V>>,
	is_active: bool,
	#[derivative(Debug="ignore")]
	#[derivative(PartialEq="ignore")]
	instance: I,
	#[derivative(Debug="ignore")]
	#[derivative(PartialEq="ignore")]
	_ph: PhantomData<S>,
}

impl<'a, K: Ord, V, S: SerializeDB, I: Default> SerializeMap<K, V, S, I> {
	/// Default but using a `SerializeDB` as parameter
	/// to resolve if the db is active.
	pub fn default_from_db(db: &S) -> Self {
		SerializeMap {
			inner: Default::default(),
			is_active: db.is_active(),
			instance: I::default(),
			_ph: PhantomData::default(),
		}
	}
}

impl<'a, K: Ord, V, S, I> SerializeMap<K, V, S, I> {
	pub fn handle(&'a mut self, db: &'a mut S) -> SerializeMapHandle<'a, K, V, S, I> {
		SerializeMapHandle {
			cache: &mut self.inner,
			collection: CollectionMut { db, instance: &self.instance },
		}
	}
}

impl<'a, K, V, S, I> SerializeMap<K, V, S, I> 
	where
		K: Codec + Ord + Clone,
		V: Codec + Clone,
		S: SerializeDB,
		I: SerializeInstanceMap,
{
	pub fn iter(&'a self, db: &'a S) -> SerializeMapIter<'a, K, V> {
		if !self.is_active {
			// There is no backing db, so all is in cache.
			SerializeMapIter::Cache(self.inner.iter())
		} else {
			// Updates happens instantanously to db, so we iterate on
			// the db.
			// We ignore cache: iter is not a fast operation.
			let collection = Collection { db, instance: &self.instance };
			SerializeMapIter::Collection(collection.iter())
		}
	}
}

pub struct SerializeMapHandle<'a, K, V, S, I> {
	cache: &'a mut BTreeMap<K, Option<V>>,
	collection: CollectionMut<'a, S, I>,
}

/// Notice that entry map does not write imediatelly but on
/// drop or on `flush`.
pub struct EntryMap<'a, K, V, S, I>
	where
		K: Encode + Ord,
		V: Codec,
		S: SerializeDB,
		I: SerializeInstanceMap,
{
	entry: sp_std::collections::btree_map::OccupiedEntry<'a, K, Option<V>>,
	collection: CollectionMut<'a, S, I>,
	need_write: bool,
	is_fetch: bool,
}

impl<'a, K, V, S, I> SerializeMapHandle<'a, K, V, S, I>
	where
		K: Encode + Clone + Ord,
		V: Codec + Clone,
		S: SerializeDB,
		I: SerializeInstanceMap,
{
	pub fn get(&mut self, k: &K) -> Option<&V> {
		if self.collection.db.is_active() {
			let collection = &self.collection;
			self.cache.entry(k.clone())
				.or_insert_with(|| {
					let enc_k = k.encode();
					collection.read(&enc_k).and_then(|v| V::decode(&mut v.as_slice()).ok())
				}).as_ref()
		} else {
			self.cache.get(k).and_then(|r|r.as_ref())
		}
	}

	pub fn remove(&mut self, k: &K) -> Option<V> {
		if !self.collection.db.is_active() {
			return self.cache.remove(k).flatten()
		}
		let mut value = match self.cache.get(k) {
			Some(None) => return None, // Delete is synch, nothing to do
			Some(Some(v)) => Some(v.clone()),
			None => None,
		};
		// We cache all deleted value
		self.cache.insert(k.clone(), None);
		let k = k.encode();
		if value.is_none() {
			// TODO see if it is the right api (we may skip this get)
			value = self.collection.read(&k).and_then(|v| V::decode(&mut v.as_slice()).ok());
		}
		self.collection.remove(k.as_slice());
		value
	}

	pub fn clear(&mut self) {
		self.cache.clear();
		self.collection.clear();
	}

	pub fn insert(&'a mut self, k: K, v: V) -> &V {
		self.collection.write(k.encode().as_slice(), v.encode().as_slice());
		let res = self.cache.entry(k)
			.and_modify(|old| *old = Some(v.clone()))
			.or_insert_with(|| Some(v));
		res.as_ref().expect("Init to some")
	}

	pub fn entry(&'a mut self, k: &K) -> EntryMap<'a, K, V, S, I> {
		let mut is_fetch = true;
		if !self.cache.contains_key(k) {
			is_fetch = false;
			self.cache.insert(k.clone(), None);
		}
		let entry = match self.cache.entry(k.clone()) {
			Entry::Occupied(o) => o,
			Entry::Vacant(..) => unreachable!("set above"),
		};
		EntryMap {
			entry,
			collection: CollectionMut {
				instance: &self.collection.instance,
				db: &mut self.collection.db,
			},
			need_write: false,
			is_fetch,
		}
	}
}

impl<'a, K, V, S, I> SerializeMapHandle<'a, K, V, S, I>
	where
		K: Codec + Clone + Ord,
		V: Codec + Clone,
		S: SerializeDB,
		I: SerializeInstanceMap,
{
	pub fn iter(&'a self) -> SerializeMapIter<'a, K, V> {
		if !self.collection.db.is_active() {
			SerializeMapIter::Cache(self.cache.iter())
		} else {
			SerializeMapIter::Collection(self.collection.iter())
		}
	}
}

pub enum SerializeMapIter<'a, K, V>
	where
		K: Codec + Ord + Clone,
		V: Codec + Clone,
{
	Cache(sp_std::collections::btree_map::Iter<'a, K, Option<V>>),
	Collection(SerializeDBIter<'a>),
}

impl<'a, K, V> Iterator for SerializeMapIter<'a, K, V>
	where
		K: Codec + Ord + Clone,
		V: Codec + Clone,
{
	type Item = (K, V);

	fn next(&mut self) -> Option<Self::Item> {
		match self {
			SerializeMapIter::Cache(i) => loop {
				match i.next() {
					Some((k, Some(v))) => return Some((k.clone(), v.clone())),
					Some((_k, None)) => (),
					None => return None,
				}
			},
			SerializeMapIter::Collection(i) => loop {
				match i.next() {
					Some((k, v)) => {
						match (K::decode(&mut k.as_slice()), V::decode(&mut v.as_slice())) {
							(Ok(k), Ok(v)) => return Some((k, v)),
							_ => (),
						}
					},
					None => return None,
				}
			},
		}
	}
}

// TODO add Eq check to avoid useless write (store the orig value and check on write only)
// (replacing is_fetch by value)
impl<'a, K, V, S, I> EntryMap<'a, K, V, S, I>
	where
		K: Encode + Clone + Ord,
		V: Codec + Clone,
		S: SerializeDB,
		I: SerializeInstanceMap,
{
	pub fn key(&self) -> &K {
		self.entry.key()
	}

	// TODO EMCH change fn once to return bool depending on wether there
	// was change done on &mut v (and change need write dependingly)
	pub fn and_modify(mut self, f: impl FnOnce(&mut V)) -> Self {
		self.fetch();

		if let Some(v) = self.entry.get_mut() {
			self.need_write = true;
			f(v)
		}
		self
	}

	pub fn or_insert_with(&mut self, value: impl FnOnce() -> V) -> &V {
		if self.entry.get().is_none() {
			*self.entry.get_mut() = Some(value());
			self.need_write = true;
		}
		self.entry.get().as_ref().expect("init above")
	}

	pub fn get(&mut self) -> Option<&V> {
		self.fetch();
		self.entry.get().as_ref()
	}

	pub fn set(&mut self, v: V) -> &V {
		self.need_write = true;
		*self.entry.get_mut() = Some(v);
		self.entry.get().as_ref().expect("init above")
	}

	pub fn clear(&mut self) {
		self.need_write = true;
		*self.entry.get_mut() = None;
		// we do not fetch
		self.is_fetch = true;
	}
}

impl<'a, K, V, S, I> EntryMap<'a, K, V, S, I>
	where
		K: Encode + Ord,
		V: Codec,
		S: SerializeDB,
		I: SerializeInstanceMap,
{
	pub fn fetch(&mut self) {
		if self.collection.db.is_active() && !self.is_fetch {
			let k = self.entry.key();
			let k = k.encode();
			let v = self.collection.read(k.as_slice())
				.and_then(|v| V::decode(&mut v.as_slice()).ok());
			*self.entry.get_mut() = v;
			self.need_write = false;
			self.is_fetch = true;
		}
	}

	pub fn flush(&mut self) {
		if self.collection.db.is_active() {
			let k = self.entry.key();
			if self.need_write {
				match self.entry.get() {
					Some(v) => {
						let k = k.encode();
						let v = v.encode();
						self.collection.write(k.as_slice(), v.as_slice());
					},
					None => {
						let k = k.encode();
						self.collection.remove(k.as_slice());
					},
				}
				self.need_write = false;
			}
		}
	}
}

impl<'a, K, V, S, I> Drop for EntryMap<'a, K, V, S, I>
	where
		K: Encode + Ord,
		V: Codec,
		S: SerializeDB,
		I: SerializeInstanceMap,
{
	fn drop(&mut self) {
		self.flush()
	}
}

#[derive(Derivative)]
#[derivative(Clone(bound="V: Clone, I: Clone"))]
#[derivative(Debug(bound="V: Debug"))]
#[derivative(Default(bound="V: Default, I: Default"))]
#[cfg_attr(test, derivative(PartialEq(bound="V: PartialEq")))]
/// Is db variable or default if undefined.
pub struct SerializeVariable<V, S, I> {
	// None indicate we did not fetch.
	inner: V,
	#[derivative(Debug="ignore")]
	#[derivative(PartialEq="ignore")]
	instance: I,
	#[derivative(Debug="ignore")]
	#[derivative(PartialEq="ignore")]
	_ph: PhantomData<S>,
}


#[derive(Derivative)]
#[derivative(Clone(bound="V: Clone, I: Clone"))]
#[derivative(Debug(bound="V: Debug"))]
#[derivative(Default(bound="V: Default, I: Default"))]
#[cfg_attr(test, derivative(PartialEq(bound="V: PartialEq")))]
/// Is db variable or default if undefined.
pub struct SerializeVariableLazy<V, S, I> {
	// None indicate we did not fetch.
	inner: Option<V>,
	#[derivative(Debug="ignore")]
	#[derivative(PartialEq="ignore")]
	instance: I,
	#[derivative(Debug="ignore")]
	#[derivative(PartialEq="ignore")]
	_ph: PhantomData<S>,
}

pub struct SerializeVariableHandleLazy<'a, V, S, I>
	where
		I: SerializeInstanceVariable,
		S: SerializeDB,
		V: Default + Codec,
{
	inner: &'a mut Option<V>,
	collection: CollectionMut<'a, S, I>,
	need_write: bool,
}

pub struct SerializeVariableHandle<'a, V, S, I>
	where
		I: SerializeInstanceVariable,
		S: SerializeDB,
		V: Default + Codec,
{
	inner: &'a mut V,
	collection: CollectionMut<'a, S, I>,
	need_write: bool,
}

impl<'a, V, S, I> SerializeVariableLazy<V, S, I>
	where
		I: SerializeInstanceVariable,
		S: SerializeDB,
		V: Default + Codec,
{
	pub fn handle(&'a mut self, db: &'a mut S) -> SerializeVariableHandleLazy<'a, V, S, I> {
		let collection = CollectionMut { db, instance: &self.instance };
		SerializeVariableHandleLazy {
			inner: &mut self.inner,
			collection,
			need_write: false,
		}
	}
}

impl<'a, V, S, I> SerializeVariable<V, S, I>
	where
		I: SerializeInstanceVariable,
		S: SerializeDB,
		V: Default + Codec,
{
	pub fn from_ser(db: &S) -> Self {
		let instance: I = Default::default();
		let collection = Collection { db, instance: &instance };
		let inner = collection.read(I::PATH).and_then(|v| V::decode(&mut v.as_slice()).ok()).unwrap_or_default();
		SerializeVariable { inner, instance: Default::default(), _ph: PhantomData }
	}

	pub fn handle(&'a mut self, db: &'a mut S) -> SerializeVariableHandle<'a, V, S, I> {
		let collection = CollectionMut { db, instance: &self.instance };
		SerializeVariableHandle {
			inner: &mut self.inner,
			collection,
			need_write: false,
		}
	}

	pub fn get(&self) -> &V {
		&self.inner
	}
}

impl<'a, V, S, I> SerializeVariableHandle<'a, V, S, I>
	where
		I: SerializeInstanceVariable,
		S: SerializeDB,
		V: Default + Codec,
{
	pub fn get(&mut self) -> &V {
		&self.inner
	}
	pub fn set(&mut self, value: V) {
		*self.inner = value;
		self.need_write = true;
	}
	pub fn flush(&mut self) {
		if self.need_write {
			let encoded = self.inner.encode();
			self.collection.write(I::PATH, encoded.as_slice());
			self.need_write = false;
		}
	}
}

impl<'a, V, S, I> Drop for SerializeVariableHandle<'a, V, S, I>
	where
		I: SerializeInstanceVariable,
		S: SerializeDB,
		V: Default + Codec,
{
	fn drop(&mut self) {
		self.flush()
	}
}

impl<'a, V, S, I> SerializeVariableHandleLazy<'a, V, S, I>
	where
		I: SerializeInstanceVariable,
		S: SerializeDB,
		V: Default + Codec,
{
	pub fn get(&mut self) -> &V {
		if self.inner.is_none() {
			*self.inner = Some(self.collection.read(I::PATH).and_then(|v| V::decode(&mut v.as_slice()).ok()).unwrap_or_default());
		}
		self.inner.as_ref().expect("Lazy init above")
	}
	pub fn set(&mut self, value: V) {
		*self.inner = Some(value);
		self.need_write = true;
	}
	pub fn flush(&mut self) {
		if self.need_write {
			let encoded = self.inner.as_ref().expect("need write only for initialized").encode();
			self.collection.write(I::PATH, encoded.as_slice());
			self.need_write = false;
		}
	}
}

impl<'a, V, S, I> Drop for SerializeVariableHandleLazy<'a, V, S, I>
	where
		I: SerializeInstanceVariable,
		S: SerializeDB,
		V: Default + Codec,
{
	fn drop(&mut self) {
		self.flush()
	}
}

/// `SerializeDB` with transaction layer.
///
/// The change are not written into the DB but into `pending` struct.
/// `pending` content should be written into the db (or transaction)
/// before commit only.
/// On revert, pending content should simply be cleared.
pub struct TransactionalSerializeDB<DB> {
	/// The pending changes and wether we need to clear collection first.
	pub pending: BTreeMap<&'static [u8], (BTreeMap<Vec<u8>, Option<Vec<u8>>>, bool)>,
	/// The inner db implementation to use.
	pub db: DB,
}

impl<DB: SerializeDB> SerializeDB for TransactionalSerializeDB<DB> {
	// Using on non active do not make much sense here.
	#[inline(always)]
	fn is_active(&self) -> bool {
		self.db.is_active()	
	}

	fn write(&mut self, c: &'static [u8], k: &[u8], v: &[u8]) {
		self.pending.entry(c)
			.or_insert_with(Default::default).0
			.insert(k.to_vec(), Some(v.to_vec()));
	}
	fn remove(&mut self, c: &'static [u8], k: &[u8]) {
		self.pending.entry(c)
			.or_insert_with(Default::default).0
			.insert(k.to_vec(), None);
	}
	fn clear(&mut self, c: &'static [u8]) {
		let col = self.pending.entry(c)
			.or_insert_with(Default::default);
		col.0.clear();
		col.1 = true;
	}
	fn read(&self, c: &'static [u8], k: &[u8]) -> Option<Vec<u8>> {
		self.pending.get(c)
			.and_then(|c| c.0.get(k).cloned())
			.or_else(|| Some(self.db.read(c, k)))
			.flatten()
	}
	fn iter<'a>(&'a self, c: &'static [u8]) -> SerializeDBIter<'a> {
		let mut clear = false;
		let mut cache = self.pending.get(c).map(|c| {
			clear = c.1;
			c.0.iter()
		});
		let next_cache = cache.as_mut()
			.and_then(|c| c.next())
			.map(|(k, v)| (k.clone(), v.clone()));
		let mut db = if clear {
			None
		} else {
			Some(self.db.iter(c))
		};
		let next_db = db.as_mut().and_then(|db| db.next());
		Box::new(TransactionalIter {
			cache,
			next_cache,
			db,
			next_db,
		})
	}
	fn contains_collection(&self, collection: &'static [u8]) -> bool {
		DB::contains_collection(&self.db, collection)
	}
}

pub struct TransactionalIter<'a> {
	cache: Option<sp_std::collections::btree_map::Iter<'a, Vec<u8>, Option<Vec<u8>>>>,
	next_cache: Option<(Vec<u8>, Option<Vec<u8>>)>,
	db: Option<SerializeDBIter<'a>>,
	next_db: Option<(Vec<u8>, Vec<u8>)>,
}

impl<'a> Iterator for TransactionalIter<'a> {
	type Item = (Vec<u8>, Vec<u8>);

	fn next(&mut self) -> Option<Self::Item> {
		enum Next {
			None,
			Cache,
			DB,
		};
		let next = match (self.next_cache.as_ref(), self.next_db.as_ref()) {
			(Some((cache_key, _)), Some((db_key, _))) => {
				match cache_key.cmp(&db_key) {
					sp_std::cmp::Ordering::Equal => {
						self.next_db = self.db.as_mut().and_then(|db| db.next());
						Next::Cache
					},
					sp_std::cmp::Ordering::Greater => {
						Next::Cache
					},
					sp_std::cmp::Ordering::Less => {
						Next::DB
					},
				}
			},
			(Some(_), None) => Next::Cache,
			(None, Some(_)) => Next::DB,
			(None, None) => Next::None,
		};
		match next {
			Next::Cache => {
				let result = self.next_cache.take();
				self.next_cache = self.cache.as_mut()
					.and_then(|c| c.next())
					.map(|(k, v)| (k.clone(), v.clone()));
				match result {
					Some((k, Some(v))) => Some((k, v)),
					Some((_k, None)) => self.next(),
					None => None,
				}
			},
			Next::DB => {
				let result = self.next_db.take();
				self.next_db = self.db.as_mut().and_then(|db| db.next());
				result
			},
			Next::None => {
				None
			},
		}
	}
}
