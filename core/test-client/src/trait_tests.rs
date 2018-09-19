use std::sync::Arc;
use keyring::Keyring;
use client::BlockOrigin;
use primitives::{Blake2Hasher, RlpCodec};
use ::TestClient;
use runtime_primitives::traits::Block as BlockT;
use backend::{self, Backend as ClientBackendT};
use blockchain::Backend as BlockChainBackendT;
use ::BlockBuilderExt;
use runtime::{self, Transfer};
use runtime_primitives::generic::BlockId;

/// helper to test the `leaves` implementation for various backends
pub fn test_leaves_for_backend<B>(backend: Arc<B>) where
	B: backend::LocalBackend<runtime::Block, Blake2Hasher, RlpCodec>,
{
	// block tree:
	// G -> A1 -> A2 -> A3 -> A4 -> A5
	//		A1 -> B2 -> B3 -> B4
	//			  B2 -> C3
	//		A1 -> D2

	let client = ::new_with_backend(backend.clone());

	let genesis_hash = client.info().unwrap().chain.genesis_hash;

	assert_eq!(
		client.backend().blockchain().leaves().unwrap(),
		vec![genesis_hash]);

	// G -> A1
	let a1 = client.new_block().unwrap().bake().unwrap();
	client.justify_and_import(BlockOrigin::Own, a1.clone()).unwrap();
	assert_eq!(
		backend.blockchain().leaves().unwrap(),
		vec![a1.hash()]);

	// A1 -> A2
	let a2 = client.new_block_at(&BlockId::Hash(a1.hash())).unwrap().bake().unwrap();
	client.justify_and_import(BlockOrigin::Own, a2.clone()).unwrap();
	assert_eq!(
		client.backend().blockchain().leaves().unwrap(),
		vec![a2.hash()]);

	// A2 -> A3
	let a3 = client.new_block_at(&BlockId::Hash(a2.hash())).unwrap().bake().unwrap();
	client.justify_and_import(BlockOrigin::Own, a3.clone()).unwrap();
	assert_eq!(
		backend.blockchain().leaves().unwrap(),
		vec![a3.hash()]);

	// A3 -> A4
	let a4 = client.new_block_at(&BlockId::Hash(a3.hash())).unwrap().bake().unwrap();
	client.justify_and_import(BlockOrigin::Own, a4.clone()).unwrap();
	assert_eq!(
		backend.blockchain().leaves().unwrap(),
		vec![a4.hash()]);

	// A4 -> A5
	let a5 = client.new_block_at(&BlockId::Hash(a4.hash())).unwrap().bake().unwrap();
	client.justify_and_import(BlockOrigin::Own, a5.clone()).unwrap();
	assert_eq!(
		backend.blockchain().leaves().unwrap(),
		vec![a5.hash()]);

	// A1 -> B2
	let mut builder = client.new_block_at(&BlockId::Hash(a1.hash())).unwrap();
	// this push is required as otherwise B2 has the same hash as A2 and won't get imported
	builder.push_transfer(Transfer {
		from: Keyring::Alice.to_raw_public().into(),
		to: Keyring::Ferdie.to_raw_public().into(),
		amount: 41,
		nonce: 0,
	}).unwrap();
	let b2 = builder.bake().unwrap();
	client.justify_and_import(BlockOrigin::Own, b2.clone()).unwrap();
	assert_eq!(
		backend.blockchain().leaves().unwrap(),
		vec![a5.hash(), b2.hash()]);

	// B2 -> B3
	let b3 = client.new_block_at(&BlockId::Hash(b2.hash())).unwrap().bake().unwrap();
	client.justify_and_import(BlockOrigin::Own, b3.clone()).unwrap();
	assert_eq!(
		backend.blockchain().leaves().unwrap(),
		vec![a5.hash(), b3.hash()]);

	// B3 -> B4
	let b4 = client.new_block_at(&BlockId::Hash(b3.hash())).unwrap().bake().unwrap();
	client.justify_and_import(BlockOrigin::Own, b4.clone()).unwrap();
	assert_eq!(
		backend.blockchain().leaves().unwrap(),
		vec![a5.hash(), b4.hash()]);

	// // B2 -> C3
	let mut builder = client.new_block_at(&BlockId::Hash(b2.hash())).unwrap();
	// this push is required as otherwise C3 has the same hash as B3 and won't get imported
	// TODO [snd] fix that this fails with Error(ApplyExtinsicFailed(Stale)
	// builder.push_transfer(Transfer {
	//	from: Keyring::Alice.to_raw_public().into(),
	//	to: Keyring::Ferdie.to_raw_public().into(),
	//	amount: 1,
	//	nonce: 0,
	// }).unwrap();
	// let c3 = builder.bake().unwrap();
	// client.justify_and_import(BlockOrigin::Own, c3.clone()).unwrap();
	// assert_eq!(
	//	backend.blockchain().leaves().unwrap(),
	//	vec![a5.hash(), b4.hash(), c3.hash()]);

	// A1 -> D2
	let mut builder = client.new_block_at(&BlockId::Hash(a1.hash())).unwrap();
	// this push is required as otherwise D2 has the same hash as B2 and won't get imported
	builder.push_transfer(Transfer {
		from: Keyring::Alice.to_raw_public().into(),
		to: Keyring::Ferdie.to_raw_public().into(),
		amount: 1,
		nonce: 0,
	}).unwrap();
	let d2 = builder.bake().unwrap();
	client.justify_and_import(BlockOrigin::Own, d2.clone()).unwrap();
	assert_eq!(
		backend.blockchain().leaves().unwrap(),
		vec![a5.hash(), b4.hash(), d2.hash()]);
}
