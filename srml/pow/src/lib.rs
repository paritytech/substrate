#![recursion_limit="128"]
#![cfg_attr(not(feature = "std"), no_std)]

pub mod diffs;
pub mod algos;

use core::marker::PhantomData;
use codec::Codec;
use pow_primitives::POW_ENGINE_ID;
use srml_support::ConsensusEngineId;

pub struct FindAuthor<V: Codec>(PhantomData<V>);

impl<V: Codec> srml_support::traits::FindAuthor<V> for FindAuthor<V> {
	fn find_author<'a, I>(digests: I) -> Option<V> where
		I: 'a + IntoIterator<Item=(ConsensusEngineId, &'a [u8])>
	{
		for (engine_id, mut value) in digests {
			if engine_id == POW_ENGINE_ID {
				return V::decode(&mut value).ok()
			}
		}

		None
	}
}
