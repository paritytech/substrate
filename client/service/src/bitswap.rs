
// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use libipld::error;
use libipld::store::{StoreResult, Store, ReadonlyStore};
pub use libipld::error::Error;
use sp_core::offchain::OffchainStorage;
use codec::{Decode, Encode};
use std::collections::HashSet;
use log::debug;

type Block = libipld::Block<libipld::codec_impl::Multicodec, libipld::Multihash>;

const BLOCK: &'static [u8] = b"bitswap_block";
const PINS: &'static [u8] = b"bitswap_pins";
const REFERRERS: &'static [u8] = b"bitswap_referrers";
const REFS: &'static [u8] = b"bitswap_refs";

/// A wrapper around an `OffchainStorage` for the purpose of storing bitswap blocks.
///
/// This is based on the implementation of the `libipld`
/// [`MemStore`](https://github.com/ipfs-rust/rust-ipld/blob/604fa5782479f322faa17d17ef3cbbb7f6e88aee/src/mem.rs#L13).
///
/// Mappings:
///
/// * `bitswap_block`: Cid -> Block bytes (`Vec<u8>`).
/// * `bitswap_pins`: Cid -> Number of pins a block has (`u64`).
/// * `bitswap_referrers`: Cid -> Number of blocks that we know refers to a block (`i64`, may be negative).
/// * `bitswap_refs`: Cid -> List of Cids a block refers to (`Vec<Cid>`)
#[derive(Clone, Debug, Default)]
pub struct BitswapStorage<S> {
	storage: S,
}

impl<S: OffchainStorage> BitswapStorage<S> {
	/// Wrap an `OffchainStorage`.
	pub fn new(storage: S) -> Self {
		Self {
			storage,
		}
	}

	fn get_any(&self, prefix: &[u8], cid: &tiny_cid::Cid) -> Result<Vec<u8>, Error> {
		self.storage.get(prefix, &cid.to_bytes()[..])
			.ok_or_else(|| error::BlockNotFound(cid.to_string()).into())
	}

	fn get_and_decode_any<D: Decode>(&self, prefix: &[u8], cid: &tiny_cid::Cid) -> Result<D, Error> {
		let bytes = self.get_any(prefix, cid)?;
		D::decode(&mut &bytes[..])
			.map_err(|error| error.into())
	}

	/// Get a block 
	pub fn get(&self, cid: &tiny_cid::Cid) -> Result<Vec<u8>, Error> {
		self.get_any(BLOCK, cid)
	}

	fn encode_and_set_any<E: Encode>(&mut self, prefix: &[u8], cid: &tiny_cid::Cid, object: E) {
		let cid_bytes = &cid.to_bytes()[..];
		let bytes = object.encode();
		self.storage.set(prefix, cid_bytes, &bytes[..]);
	}

	fn modify_referrers(&mut self, cid: &tiny_cid::Cid, n: i64) {
		let referrers = self.get_and_decode_any::<i64>(REFERRERS, cid).unwrap_or(0);
		self.encode_and_set_any(REFERRERS, cid, referrers + n);
	}

	fn pin(&mut self, cid: &tiny_cid::Cid) {
		let mut pins = self.get_and_decode_any::<u64>(PINS, cid).unwrap_or(0);
		pins += 1;
		debug!("Pinning {}. Pins: {}.", cid, pins);
		self.encode_and_set_any(PINS, cid, pins);
	}

	/// Remove a pin from a block, removing it from the storage if it's the last pin.
	pub fn unpin(&mut self, cid: &tiny_cid::Cid) -> Result<(), Error> {
		let mut pins = self.get_and_decode_any::<u64>(PINS, cid)?;
		pins -= 1;
		self.encode_and_set_any(PINS, cid, pins);

		debug!("Unpinning {}. Pins: {}", cid, pins);

		if pins == 0 {
			self.remove(cid)?;
		}

		Ok(())
	}

	fn get_refs(&self, cid: &tiny_cid::Cid) -> Result<Vec<tiny_cid::Cid>, Error> {
		self.get_and_decode_any::<Vec<Vec<u8>>>(REFS, cid)?
			.into_iter()
			.map(|bytes| {
				use std::convert::TryFrom;
				tiny_cid::Cid::try_from(bytes)
					.map_err(|err| err.into())

			})
			.collect()
	}

	fn set_refs(&mut self, cid: &tiny_cid::Cid, refs: HashSet<tiny_cid::Cid>) {
		let vec: Vec<Vec<u8>> = refs
			.into_iter()
			.map(|cid| cid.to_bytes())
			.collect();

		self.encode_and_set_any(REFS, cid, vec);
	}

	fn remove(&mut self, cid: &tiny_cid::Cid) -> Result<(), Error> {
		let pins = self.get_and_decode_any::<u64>(PINS, cid).unwrap_or_default();
		let referrers = self.get_and_decode_any::<i64>(REFERRERS, cid).unwrap_or_default();

		debug!("Removing {}. Pins: {}, referrers: {}", cid, pins, referrers);

		if referrers < 1 && pins < 1 {
			let cid_bytes = &cid.to_bytes()[..];

			let refs = self.get_refs(cid)?;

			self.storage.remove(REFERRERS, cid_bytes);
			self.storage.remove(BLOCK, cid_bytes);
			self.storage.remove(PINS, cid_bytes);
			self.storage.remove(REFS, cid_bytes);

			for cid in &refs {
				self.modify_referrers(cid, -1);
				self.remove(cid)?;
			}
		}

		Ok(())
	}

	/// Insert an ipld block into the storage and pin it.
	pub fn insert_and_pin(&mut self, cid: &tiny_cid::Cid, data: Box<[u8]>) -> Result<(), Error> {
		self.insert(cid, data)?;
		self.pin(cid);
		Ok(())
	} 

	/// Insert an ipld block into the storage.
	pub fn insert(&mut self, cid: &tiny_cid::Cid, data: Box<[u8]>) -> Result<(), Error> {
		if self.get_any(BLOCK, cid).is_ok() {
			return Ok(())
		}

		debug!("Inserting {} into storage.", cid);

		let ipld = Block::new(cid.clone(), data.clone()).decode_ipld()?;
		let refs = ipld.references();
		
		for cid in &refs {
			self.modify_referrers(cid, 1);
		}

		self.set_refs(cid, refs);

		let cid_bytes = &cid.to_bytes()[..];
		self.storage.set(BLOCK, cid_bytes, &data);

		Ok(())
	}
	
	fn insert_batch_inner(&mut self, batch: &[Block]) -> Result<tiny_cid::Cid, Error> {
		let mut last_cid = None;
		for Block { cid, data, .. } in batch.iter().cloned() {
			self.insert(&cid, data)?;
			last_cid = Some(cid);
		}
		Ok(last_cid.ok_or(error::EmptyBatch)?)
	}
}

impl<T: OffchainStorage> ReadonlyStore for BitswapStorage<T> {
	const MAX_BLOCK_SIZE: usize = libipld::MAX_BLOCK_SIZE;
	
	type Multihash = libipld::Multihash;
	type Codec = libipld::codec_impl::Multicodec;

	fn get<'a>(&'a self, cid: tiny_cid::Cid) -> StoreResult<'a, Block> {
		Box::pin(async move {
			let vec = self.get_any(BLOCK, &cid)?;
			let block = Block::new(cid, vec.into_boxed_slice());
			Ok(block)
		})
	}
}

impl<T: OffchainStorage> Store for BitswapStorage<T> {
	fn flush(&self) -> StoreResult<'_, ()> {
		Box::pin(async move { Ok(()) })
	}
	
	fn insert<'a>(
		&'a self,
		block: &'a Block,
	) -> StoreResult<'a, ()> {
		Box::pin(async move {
			BitswapStorage::insert(&mut self.clone(), &block.cid, block.data.clone())?;
			self.clone().pin(&block.cid);
			Ok(())
		})
	}
	
	fn insert_batch<'a>(
		&'a self,
		batch: &'a [Block],
	) -> StoreResult<'a, tiny_cid::Cid> {
		Box::pin(async move { 
			self.clone().insert_batch_inner(batch)
		 })
	}

	fn unpin<'a>(&'a self, cid: &'a tiny_cid::Cid) -> StoreResult<'a, ()> {
		Box::pin(async move {
			BitswapStorage::unpin(&mut self.clone(), cid)
		})
	}
}

// These tests are copied from
// https://github.com/ipfs-rust/rust-ipld/blob/604fa5782479f322faa17d17ef3cbbb7f6e88aee/src/mem.rs#L221.
#[cfg(test)]
mod tests {
    use super::*;
	use libipld::codec_impl::Multicodec;
	use tiny_cid::Cid;
    use libipld::ipld;
    use libipld::ipld::Ipld;
    use libipld::multihash::SHA2_256;
	use libipld::store::Store;
	use libipld::error::BlockNotFound;
	use sp_core::offchain::testing::TestPersistentOffchainDB;
	type Storage = BitswapStorage<TestPersistentOffchainDB>;

    async fn get<S: ReadonlyStore>(store: &S, cid: &Cid) -> Option<Ipld>
    where
        Ipld: libipld::codec::Decode<S::Codec>,
    {
        let block = match store.get(cid.clone()).await {
            Ok(block) => block,
            Err(e) if e.downcast_ref::<BlockNotFound>().is_some() => return None,
            Err(e) => Err(e).unwrap(),
        };
        let ipld = block.decode::<_, Ipld>().unwrap();
        Some(ipld)
    }

    async fn insert<S: Store<Multihash = libipld::Multihash, Codec = Multicodec>>(store: &S, ipld: &Ipld) -> Cid
    where
        S::Codec: From<Multicodec>,
    {
        let block = Block::encode(Multicodec::DagCbor, SHA2_256, ipld).unwrap();
        store.insert(&block).await.unwrap();
        block.cid
    }

    #[async_std::test]
    async fn bitswap_garbage_collection() {
        let _ = env_logger::try_init();
		let store = Storage::default();
        let a = insert(&store, &ipld!({ "a": [] })).await;
        let b = insert(&store, &ipld!({ "b": [&a] })).await;
        store.unpin(&a).await.unwrap();
        let c = insert(&store, &ipld!({ "c": [&a] })).await;
        assert!(get(&store, &a).await.is_some());
        assert!(get(&store, &b).await.is_some());
        assert!(get(&store, &c).await.is_some());
        store.unpin(&b).await.unwrap();
        assert!(get(&store, &a).await.is_some());
        assert!(get(&store, &b).await.is_none());
        assert!(get(&store, &c).await.is_some());
        store.unpin(&c).await.unwrap();
        assert!(get(&store, &a).await.is_none());
        assert!(get(&store, &b).await.is_none());
        assert!(get(&store, &c).await.is_none());
    }

    #[async_std::test]
    async fn bitswap_garbage_collection_2() {
        let _ = env_logger::try_init();
		let store = Storage::default();
        let a = insert(&store, &ipld!({ "a": [] })).await;
        let b = insert(&store, &ipld!({ "b": [&a] })).await;
        store.unpin(&a).await.unwrap();
        let c = insert(&store, &ipld!({ "b": [&a] })).await;
        assert!(get(&store, &a).await.is_some());
        assert!(get(&store, &b).await.is_some());
        assert!(get(&store, &c).await.is_some());
        store.unpin(&b).await.unwrap();
        assert!(get(&store, &a).await.is_some());
        assert!(get(&store, &b).await.is_some());
        assert!(get(&store, &c).await.is_some());
        store.unpin(&c).await.unwrap();
        assert!(get(&store, &a).await.is_none());
        assert!(get(&store, &b).await.is_none());
        assert!(get(&store, &c).await.is_none());
    }
}
