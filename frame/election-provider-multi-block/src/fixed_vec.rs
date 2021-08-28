use std::fmt::Debug;

use codec::{Decode, Encode, EncodeLike, MaxEncodedLen};
use frame_election_provider_support::PageIndex;
use frame_support::traits::Get;
use sp_std::{
	convert::TryFrom,
	fmt,
	iter::IntoIterator,
	marker::PhantomData,
	ops::{Deref, Index, IndexMut},
	slice::SliceIndex,
};

#[derive(Encode, Decode)]
pub struct FixedVec<T, S>(Vec<T>, PhantomData<S>);

impl<T, S> Clone for FixedVec<T, S>
where
	T: Clone,
{
	fn clone(&self) -> Self {
		Self::unchecked_from(self.0.clone())
	}
}

impl<T, S: Get<PageIndex>> TryFrom<Vec<T>> for FixedVec<T, S> {
	type Error = ();
	fn try_from(t: Vec<T>) -> Result<Self, Self::Error> {
		if t.len() == Self::size() {
			Ok(Self::unchecked_from(t))
		} else {
			Err(())
		}
	}
}

impl<T: Default, S: Get<PageIndex>> Default for FixedVec<T, S> {
	fn default() -> Self {
		let mut src: Vec<T> = Vec::with_capacity(Self::size());
		for _ in 0..Self::size() {
			src.push(Default::default())
		}
		Self::try_new(src).unwrap()
	}
}

impl<T, S> AsRef<Vec<T>> for FixedVec<T, S> {
	fn as_ref(&self) -> &Vec<T> {
		&self.0
	}
}

impl<T, S> AsRef<[T]> for FixedVec<T, S> {
	fn as_ref(&self) -> &[T] {
		&self.0
	}
}

impl<T, S> AsMut<[T]> for FixedVec<T, S> {
	fn as_mut(&mut self) -> &mut [T] {
		&mut self.0
	}
}

impl<T, S> Deref for FixedVec<T, S> {
	type Target = Vec<T>;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

impl<T, S, I> Index<I> for FixedVec<T, S>
where
	I: SliceIndex<[T]>,
{
	type Output = I::Output;

	#[inline]
	fn index(&self, index: I) -> &Self::Output {
		self.0.index(index)
	}
}

impl<T, S, I> IndexMut<I> for FixedVec<T, S>
where
	I: SliceIndex<[T]>,
{
	#[inline]
	fn index_mut(&mut self, index: I) -> &mut Self::Output {
		self.0.index_mut(index)
	}
}

impl<T, S> IntoIterator for FixedVec<T, S> {
	type Item = T;
	type IntoIter = sp_std::vec::IntoIter<T>;
	fn into_iter(self) -> Self::IntoIter {
		self.0.into_iter()
	}
}

impl<T, S> PartialEq for FixedVec<T, S>
where
	T: PartialEq,
{
	fn eq(&self, rhs: &Self) -> bool {
		self.0 == rhs.0
	}
}

impl<T: PartialEq, S: Get<PageIndex>> PartialEq<Vec<T>> for FixedVec<T, S> {
	fn eq(&self, other: &Vec<T>) -> bool {
		&self.0 == other
	}
}

impl<T, S> Eq for FixedVec<T, S> where T: Eq {}

#[cfg(feature = "std")]
impl<T, S> fmt::Debug for FixedVec<T, S>
where
	T: fmt::Debug,
	S: Get<PageIndex>,
{
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.debug_tuple("FixedVec").field(&self.0).field(&Self::size()).finish()
	}
}

impl<T, S> FixedVec<T, S> {
	fn unchecked_from(src: Vec<T>) -> Self {
		Self(src, Default::default())
	}
}

impl<T, S: Get<PageIndex>> FixedVec<T, S> {
	pub fn size() -> usize {
		S::get().into()
	}

	pub fn try_new(src: Vec<T>) -> Result<Self, ()> {
		if src.len() == Self::size() {
			Ok(Self::unchecked_from(src))
		} else {
			Err(())
		}
	}

	pub fn filling_new(mut src: Vec<T>, placeholder: T) -> Result<Self, ()>
	where
		T: Clone,
	{
		if src.len() > Self::size() {
			return Err(())
		}
		while src.len() < Self::size() {
			src.insert(0, placeholder.clone())
		}
		debug_assert!(src.len() == Self::size());
		Ok(Self::unchecked_from(src))
	}

	pub fn inner(self) -> Vec<T> {
		self.0
	}
}
