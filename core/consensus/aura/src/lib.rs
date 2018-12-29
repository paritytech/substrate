// Copyright 2018 Parity Technologies (UK) Ltd.
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

//! Aura (Authority-round) consensus in substrate.
//!
//! Aura works by having a list of authorities A who are expected to roughly
//! agree on the current time. Time is divided up into discrete slots of t
//! seconds each. For each slot s, the author of that slot is A[s % |A|].
//!
//! The author is allowed to issue one block but not more during that slot,
//! and it will be built upon the longest valid chain that has been seen.
//!
//! Blocks from future steps will be either deferred or rejected depending on how
//! far in the future they are.

extern crate parity_codec as codec;
extern crate substrate_client as client;
extern crate substrate_primitives as primitives;
extern crate srml_support as runtime_support;
extern crate sr_io as runtime_io;
extern crate sr_primitives as runtime_primitives;
extern crate substrate_consensus_aura_primitives as aura_primitives;

extern crate substrate_consensus_common as consensus_common;
extern crate tokio;
extern crate sr_version as runtime_version;
extern crate substrate_network as network;
extern crate parking_lot;

#[macro_use]
extern crate log;
#[macro_use]
extern crate futures;

#[cfg(test)]
extern crate substrate_keyring as keyring;
#[cfg(test)]
extern crate substrate_service as service;
#[cfg(test)]
extern crate substrate_test_client as test_client;
#[cfg(test)]
extern crate env_logger;

mod slots;

use std::sync::Arc;
use std::time::Duration;

use codec::Encode;
use consensus_common::{Authorities, BlockImport, Environment, Proposer};
use client::ChainHead;
use client::block_builder::api::BlockBuilder as BlockBuilderApi;
use consensus_common::{ImportBlock, BlockOrigin};
use runtime_primitives::{generic, generic::BlockId, Justification, BasicInherentData};
use runtime_primitives::traits::{Block, Header, Digest, DigestItemFor, ProvideRuntimeApi};
use network::import_queue::{Verifier, BasicQueue};
use primitives::{AuthorityId, ed25519};

use futures::{Stream, Future, IntoFuture, future::{self, Either}};
use tokio::timer::Timeout;
use api::AuraApi;
use slots::Slots;

pub use aura_primitives::*;
pub use consensus_common::SyncOracle;

/// A handle to the network. This is generally implemented by providing some
/// handle to a gossip service or similar.
///
/// Intended to be a lightweight handle such as an `Arc`.
pub trait Network: Clone {
	/// A stream of input messages for a topic.
	type In: Stream<Item=Vec<u8>,Error=()>;

	/// Send a message at a specific round out.
	fn send_message(&self, slot: u64, message: Vec<u8>);
}

/// Get slot author for given block along with authorities.
fn slot_author(slot_num: u64, authorities: &[AuthorityId]) -> Option<AuthorityId> {
	if authorities.is_empty() { return None }

	let idx = slot_num % (authorities.len() as u64);
	assert!(idx <= usize::max_value() as u64,
		"It is impossible to have a vector with length beyond the address space; qed");

	let current_author = *authorities.get(idx as usize)
		.expect("authorities not empty; index constrained to list length;\
				this is a valid index; qed");

	Some(current_author)
}

fn duration_now() -> Option<Duration> {
	use std::time::SystemTime;

	let now = SystemTime::now();
	now.duration_since(SystemTime::UNIX_EPOCH).map_err(|e| {
			warn!("Current time {:?} is before unix epoch. Something is wrong: {:?}", now, e);
	}).ok()
}

fn timestamp_and_slot_now(slot_duration: u64) -> Option<(u64, u64)> {
	duration_now().map(|s| {
		let s = s.as_secs();
		(s, s / slot_duration)
	})
}

/// Get the slot for now.
fn slot_now(slot_duration: u64) -> Option<u64> {
	duration_now().map(|s| s.as_secs() / slot_duration)
}

/// A digest item which is usable with aura consensus.
pub trait CompatibleDigestItem: Sized {
	/// Construct a digest item which is a slot number and a signature on the
	/// hash.
	fn aura_seal(slot_number: u64, signature: ed25519::Signature) -> Self;

	/// If this item is an Aura seal, return the slot number and signature.
	fn as_aura_seal(&self) -> Option<(u64, &ed25519::Signature)>;
}

impl<Hash, AuthorityId> CompatibleDigestItem for generic::DigestItem<Hash, AuthorityId> {
	/// Construct a digest item which is a slot number and a signature on the
	/// hash.
	fn aura_seal(slot_number: u64, signature: ed25519::Signature) -> Self {
		generic::DigestItem::Seal(slot_number, signature)
	}
	/// If this item is an Aura seal, return the slot number and signature.
	fn as_aura_seal(&self) -> Option<(u64, &ed25519::Signature)> {
		match self {
			generic::DigestItem::Seal(slot, ref sign) => Some((*slot, sign)),
			_ => None
		}
	}
}

/// Start the aura worker in a separate thread.
pub fn start_aura_thread<B, C, E, I, SO, Error>(
	slot_duration: SlotDuration,
	local_key: Arc<ed25519::Pair>,
	client: Arc<C>,
	block_import: Arc<I>,
	env: Arc<E>,
	sync_oracle: SO,
	on_exit: impl Future<Item=(),Error=()> + Send + 'static,
) where
	B: Block + 'static,
	C: Authorities<B> + ChainHead<B> + Send + Sync + 'static,
	E: Environment<B, AuraConsensusData, Error=Error> + Send + Sync + 'static,
	E::Proposer: Proposer<B, AuraConsensusData, Error=Error> + 'static,
	I: BlockImport<B> + Send + Sync + 'static,
	Error: From<C::Error> + From<I::Error> + 'static,
	SO: SyncOracle + Send + Clone + 'static,
	DigestItemFor<B>: CompatibleDigestItem + 'static,
	Error: ::std::error::Error + Send + From<::consensus_common::Error> + 'static,
{
	use tokio::runtime::current_thread::Runtime;

	::std::thread::spawn(move || {
		let mut runtime = match Runtime::new() {
			Ok(r) => r,
			Err(e) => {
				warn!("Unable to start authorship: {:?}", e);
				return;
			}
		};

		let _ = runtime.block_on(start_aura(
			slot_duration,
			local_key,
			client,
			block_import,
			env,
			sync_oracle,
			on_exit,
		));
	});
}

/// Start the aura worker. The returned future should be run in a tokio runtime.
pub fn start_aura<B, C, E, I, SO, Error>(
	slot_duration: SlotDuration,
	local_key: Arc<ed25519::Pair>,
	client: Arc<C>,
	block_import: Arc<I>,
	env: Arc<E>,
	sync_oracle: SO,
	on_exit: impl Future<Item=(),Error=()>,
) -> impl Future<Item=(),Error=()> where
	B: Block,
	C: Authorities<B> + ChainHead<B>,
	E: Environment<B, AuraConsensusData, Error=Error>,
	E::Proposer: Proposer<B, AuraConsensusData, Error=Error>,
	I: BlockImport<B>,
	Error: From<C::Error> + From<I::Error>,
	SO: SyncOracle + Send + Clone,
	DigestItemFor<B>: CompatibleDigestItem,
	Error: ::std::error::Error + Send + 'static + From<::consensus_common::Error>,
{
	let make_authorship = move || {
		use futures::future;

		let client = client.clone();
		let pair = local_key.clone();
		let block_import = block_import.clone();
		let env = env.clone();
		let sync_oracle = sync_oracle.clone();
		let SlotDuration(slot_duration) = slot_duration;

		// rather than use a timer interval, we schedule our waits ourselves
		Slots::new(slot_duration)
			.map_err(|e| debug!(target: "aura", "Faulty timer: {:?}", e))
			.for_each(move |slot_info| {
				let client = client.clone();
				let pair = pair.clone();
				let block_import = block_import.clone();
				let env = env.clone();
				let sync_oracle = sync_oracle.clone();
				let public_key = pair.public();

				// only propose when we are not syncing.
				if sync_oracle.is_major_syncing() {
					debug!(target: "aura", "Skipping proposal slot due to sync.");
					return Either::B(future::ok(()));
				}

				let (timestamp, slot_num) = (slot_info.timestamp, slot_info.number);
				let chain_head = match client.best_block_header() {
					Ok(x) => x,
					Err(e) => {
						warn!(target:"aura", "Unable to author block in slot {}. \
							no best block header: {:?}", slot_num, e);
						return Either::B(future::ok(()))
					}
				};

				let authorities = match client.authorities(&BlockId::Hash(chain_head.hash())) {
					Ok(authorities) => authorities,
					Err(e) => {
						warn!("Unable to fetch authorities at\
							block {:?}: {:?}", chain_head.hash(), e);
						return Either::B(future::ok(()));
					}
				};

				let proposal_work = match slot_author(slot_num, &authorities) {
					None => return Either::B(future::ok(())),
					Some(author) => if author.0 == public_key.0 {
						debug!(target: "aura", "Starting authorship at slot {}; timestamp = {}",
							slot_num, timestamp);

						// we are the slot author. make a block and sign it.
						let proposer = match env.init(&chain_head, &authorities, pair.clone()) {
							Ok(p) => p,
							Err(e) => {
								warn!("Unable to author block in slot {:?}: {:?}", slot_num, e);
								return Either::B(future::ok(()))
							}
						};

						let consensus_data = AuraConsensusData {
							timestamp,
							slot: slot_num,
							slot_duration,
						};

						// deadline our production to approx. the end of the
						// slot
						Timeout::new(
							proposer.propose(consensus_data).into_future(),
							slot_info.remaining_duration(),
						)
					} else {
						return Either::B(future::ok(()));
					}
				};

				let block_import = block_import.clone();
				Either::A(proposal_work
					.map(move |b| {
						// minor hack since we don't have access to the timestamp
						// that is actually set by the proposer.
						let slot_after_building = slot_now(slot_duration);
						if slot_after_building != Some(slot_num) {
							info!("Discarding proposal for slot {}; block production took too long",
								slot_num);
							return
						}

						let (header, body) = b.deconstruct();
						let pre_hash = header.hash();
						let parent_hash = header.parent_hash().clone();

						// sign the pre-sealed hash of the block and then
						// add it to a digest item.
						let to_sign = (slot_num, pre_hash).encode();
						let signature = pair.sign(&to_sign[..]);
						let item = <DigestItemFor<B> as CompatibleDigestItem>::aura_seal(
							slot_num,
							signature,
						);

						let import_block = ImportBlock {
							origin: BlockOrigin::Own,
							header,
							justification: None,
							post_digests: vec![item],
							body: Some(body),
							finalized: false,
							auxiliary: Vec::new(),
						};

						if let Err(e) = block_import.import_block(import_block, None) {
							warn!(target: "aura", "Error with block built on {:?}: {:?}",
								parent_hash, e);
						}
					})
					.map_err(|e| warn!("Failed to construct block: {:?}", e))
				)
			})
	};

	let work = future::loop_fn((), move |()| {
		let authorship_task = ::std::panic::AssertUnwindSafe(make_authorship());
		authorship_task.catch_unwind().then(|res| {
			match res {
				Ok(Ok(())) => (),
				Ok(Err(())) => warn!("Aura authorship task terminated unexpectedly. Restarting"),
				Err(e) => {
					if let Some(s) = e.downcast_ref::<&'static str>() {
						warn!("Aura authorship task panicked at {:?}", s);
					}

					warn!("Restarting Aura authorship task");
				}
			}

			Ok(future::Loop::Continue(()))
		})
	});

	work.select(on_exit).then(|_| Ok(()))
}

// a header which has been checked
enum CheckedHeader<H> {
	// a header which has slot in the future. this is the full header (not stripped)
	// and the slot in which it should be processed.
	Deferred(H, u64),
	// a header which is fully checked, including signature. This is the pre-header
	// accompanied by the seal components.
	Checked(H, u64, ed25519::Signature),
}

/// check a header has been signed by the right key. If the slot is too far in the future, an error will be returned.
/// if it's successful, returns the pre-header, the slot number, and the signat.
//
// FIXME: needs misbehavior types - https://github.com/paritytech/substrate/issues/1018
fn check_header<B: Block>(slot_now: u64, mut header: B::Header, hash: B::Hash, authorities: &[AuthorityId])
	-> Result<CheckedHeader<B::Header>, String>
	where DigestItemFor<B>: CompatibleDigestItem
{
	let digest_item = match header.digest_mut().pop() {
		Some(x) => x,
		None => return Err(format!("Header {:?} is unsealed", hash)),
	};
	let (slot_num, &sig) = match digest_item.as_aura_seal() {
		Some(x) => x,
		None => return Err(format!("Header {:?} is unsealed", hash)),
	};

	if slot_num > slot_now {
		header.digest_mut().push(digest_item);
		Ok(CheckedHeader::Deferred(header, slot_num))
	} else {
		// check the signature is valid under the expected authority and
		// chain state.

		let expected_author = match slot_author(slot_num, &authorities) {
			None => return Err("Slot Author not found".to_string()),
			Some(author) => author
		};

		let pre_hash = header.hash();
		let to_sign = (slot_num, pre_hash).encode();
		let public = ed25519::Public(expected_author.0);

		if ed25519::verify_strong(&sig, &to_sign[..], public) {
			Ok(CheckedHeader::Checked(header, slot_num, sig))
		} else {
			Err(format!("Bad signature on {:?}", hash))
		}
	}
}

/// Extra verification for Aura blocks.
pub trait ExtraVerification<B: Block>: Send + Sync {
	/// Future that resolves when the block is verified or fails with error if not.
	type Verified: IntoFuture<Item=(),Error=String>;

	/// Do additional verification for this block.
	fn verify(
		&self,
		header: &B::Header,
		body: Option<&[B::Extrinsic]>,
	) -> Self::Verified;
}

/// A verifier for Aura blocks.
pub struct AuraVerifier<C, E, MakeInherent> {
	slot_duration: SlotDuration,
	client: Arc<C>,
	make_inherent: MakeInherent,
	extra: E,
}

/// No-op extra verification.
#[derive(Debug, Clone, Copy)]
pub struct NothingExtra;

impl<B: Block> ExtraVerification<B> for NothingExtra {
	type Verified = Result<(), String>;

	fn verify(&self, _: &B::Header, _: Option<&[B::Extrinsic]>) -> Self::Verified {
		Ok(())
	}
}

impl<B: Block, C, E, MakeInherent, Inherent> Verifier<B> for AuraVerifier<C, E, MakeInherent> where
	C: Authorities<B> + BlockImport<B> + ProvideRuntimeApi + Send + Sync,
	C::Api: BlockBuilderApi<B, Inherent>,
	DigestItemFor<B>: CompatibleDigestItem,
	E: ExtraVerification<B>,
	MakeInherent: Fn(u64, u64) -> Inherent + Send + Sync,
{
	fn verify(
		&self,
		origin: BlockOrigin,
		header: B::Header,
		justification: Option<Justification>,
		mut body: Option<Vec<B::Extrinsic>>,
	) -> Result<(ImportBlock<B>, Option<Vec<AuthorityId>>), String> {
		use runtime_primitives::CheckInherentError;
		const MAX_TIMESTAMP_DRIFT_SECS: u64 = 60;

		let (timestamp_now, slot_now) = timestamp_and_slot_now(self.slot_duration.0)
			.ok_or("System time is before UnixTime?".to_owned())?;
		let hash = header.hash();
		let parent_hash = *header.parent_hash();
		let authorities = self.client.authorities(&BlockId::Hash(parent_hash))
			.map_err(|e| format!("Could not fetch authorities at {:?}: {:?}", parent_hash, e))?;

		let extra_verification = self.extra.verify(
			&header,
			body.as_ref().map(|x| &x[..]),
		);

		// we add one to allow for some small drift.
		// FIXME: in the future, alter this queue to allow deferring of headers
		// https://github.com/paritytech/substrate/issues/1019
		let checked_header = check_header::<B>(slot_now + 1, header, hash, &authorities[..])?;
		match checked_header {
			CheckedHeader::Checked(pre_header, slot_num, sig) => {
				let item = <DigestItemFor<B>>::aura_seal(slot_num, sig);

				// if the body is passed through, we need to use the runtime
				// to check that the internally-set timestamp in the inherents
				// actually matches the slot set in the seal.
				if let Some(inner_body) = body.take() {
					let inherent = (self.make_inherent)(timestamp_now, slot_num);
					let block = Block::new(pre_header.clone(), inner_body);

					let inherent_res = self.client.runtime_api().check_inherents(
						&BlockId::Hash(parent_hash),
						&block,
						&inherent,
					).map_err(|e| format!("{:?}", e))?;

					match inherent_res {
						Ok(()) => {}
						Err(CheckInherentError::ValidAtTimestamp(timestamp)) => {
							// halt import until timestamp is valid.
							// reject when too far ahead.
							if timestamp > timestamp_now + MAX_TIMESTAMP_DRIFT_SECS {
								return Err("Rejecting block too far in future".into());
							}

							let diff = timestamp.saturating_sub(timestamp_now);
							info!(target: "aura", "halting for block {} seconds in the future", diff);
							::std::thread::sleep(Duration::from_secs(diff));
						},
						Err(CheckInherentError::Other(s)) => return Err(s.into_owned()),
					}

					let (_, inner_body) = block.deconstruct();
					body = Some(inner_body);
				}

				trace!(target: "aura", "Checked {:?}; importing.", pre_header);

				extra_verification.into_future().wait()?;

				let import_block = ImportBlock {
					origin,
					header: pre_header,
					post_digests: vec![item],
					body,
					finalized: false,
					justification,
					auxiliary: Vec::new(),
				};

				// FIXME: extract authorities - https://github.com/paritytech/substrate/issues/1019
				Ok((import_block, None))
			}
			CheckedHeader::Deferred(a, b) => {
				debug!(target: "aura", "Checking {:?} failed; {:?}, {:?}.", hash, a, b);
				Err(format!("Header {:?} rejected: too far in the future", hash))
			}
		}
	}
}

/// A utility for making the basic-inherent data.
pub fn make_basic_inherent(timestamp: u64, slot_now: u64) -> BasicInherentData {
	BasicInherentData::new(timestamp, slot_now)
}

/// A type for a function which produces inherent.
pub type InherentProducingFn<I> = fn(u64, u64) -> I;

/// The Aura import queue type.
pub type AuraImportQueue<B, C, E, MakeInherent> = BasicQueue<B, AuraVerifier<C, E, MakeInherent>>;

/// A slot duration. Create with `get_or_compute`.
// The internal member should stay private here.
#[derive(Clone, Copy, Debug)]
pub struct SlotDuration(u64);

impl SlotDuration {
	/// Either fetch the slot duration from disk or compute it from the genesis
	/// state.
	pub fn get_or_compute<B: Block, C>(client: &C) -> ::client::error::Result<Self> where
		C: ::client::backend::AuxStore,
		C: ProvideRuntimeApi,
		C::Api: AuraApi<B>,
	{
		use codec::Decode;
		const SLOT_KEY: &[u8] = b"aura_slot_duration";

		match client.get_aux(SLOT_KEY)? {
			Some(v) => u64::decode(&mut &v[..])
				.map(SlotDuration)
				.ok_or_else(|| ::client::error::ErrorKind::Backend(
					format!("Aura slot duration kept in invalid format"),
				).into()),
			None => {
				use runtime_primitives::traits::Zero;
				let genesis_slot_duration = client.runtime_api()
					.slot_duration(&BlockId::number(Zero::zero()))?;

				info!("Loaded block-time = {:?} seconds from genesis on first-launch",
					genesis_slot_duration);

				genesis_slot_duration.using_encoded(|s| {
					client.insert_aux(&[(SLOT_KEY, &s[..])], &[])
				})?;

				Ok(SlotDuration(genesis_slot_duration))
			}
		}
	}
}

/// Start an import queue for the Aura consensus algorithm.
pub fn import_queue<B, C, E, MakeInherent, Inherent>(
	slot_duration: SlotDuration,
	client: Arc<C>,
	extra: E,
	make_inherent: MakeInherent,
) -> AuraImportQueue<B, C, E, MakeInherent> where
	B: Block,
	C: Authorities<B> + BlockImport<B,Error=::client::error::Error> + ProvideRuntimeApi + Send + Sync,
	C::Api: BlockBuilderApi<B, Inherent>,
	DigestItemFor<B>: CompatibleDigestItem,
	E: ExtraVerification<B>,
	MakeInherent: Fn(u64, u64) -> Inherent + Send + Sync,
{
	let verifier = Arc::new(AuraVerifier { slot_duration, client: client.clone(), extra, make_inherent });
	BasicQueue::new(verifier, client)
}

#[cfg(test)]
mod tests {
	use super::*;
	use consensus_common::NoNetwork as DummyOracle;
	use network::test::*;
	use network::test::{Block as TestBlock, PeersClient};
	use runtime_primitives::traits::Block as BlockT;
	use network::config::ProtocolConfig;
	use parking_lot::Mutex;
	use tokio::runtime::current_thread;
	use keyring::Keyring;
	use client::BlockchainEvents;
	use test_client;

	type Error = ::client::error::Error;

	type TestClient = ::client::Client<test_client::Backend, test_client::Executor, TestBlock, test_client::runtime::RuntimeApi>;

	struct DummyFactory(Arc<TestClient>);
	struct DummyProposer(u64, Arc<TestClient>);

	impl Environment<TestBlock, AuraConsensusData> for DummyFactory {
		type Proposer = DummyProposer;
		type Error = Error;

		fn init(&self, parent_header: &<TestBlock as BlockT>::Header, _authorities: &[AuthorityId], _sign_with: Arc<ed25519::Pair>)
			-> Result<DummyProposer, Error>
		{
			Ok(DummyProposer(parent_header.number + 1, self.0.clone()))
		}
	}

	impl Proposer<TestBlock, AuraConsensusData> for DummyProposer {
		type Error = Error;
		type Create = Result<TestBlock, Error>;

		fn propose(&self, _consensus_data: AuraConsensusData) -> Result<TestBlock, Error> {
			self.1.new_block().unwrap().bake().map_err(|e| e.into())
		}
	}

	const SLOT_DURATION: u64 = 1;
	const TEST_ROUTING_INTERVAL: Duration = Duration::from_millis(50);

	pub struct AuraTestNet {
		peers: Vec<Arc<Peer<AuraVerifier<
			PeersClient,
			NothingExtra,
			InherentProducingFn<()>,
		>, ()>>>,
		started: bool
	}

	impl TestNetFactory for AuraTestNet {
		type Verifier = AuraVerifier<PeersClient, NothingExtra, InherentProducingFn<()>>;
		type PeerData = ();

		/// Create new test network with peers and given config.
		fn from_config(_config: &ProtocolConfig) -> Self {
			AuraTestNet {
				peers: Vec::new(),
				started: false
			}
		}

		fn make_verifier(&self, client: Arc<PeersClient>, _cfg: &ProtocolConfig)
			-> Arc<Self::Verifier>
		{
			fn make_inherent(_: u64, _: u64) { () }
			let slot_duration = SlotDuration::get_or_compute(&*client)
				.expect("slot duration available");

			assert_eq!(slot_duration.0, SLOT_DURATION);
			Arc::new(AuraVerifier {
				client,
				slot_duration,
				extra: NothingExtra,
				make_inherent: make_inherent as _,
			})
		}

		fn peer(&self, i: usize) -> &Peer<Self::Verifier, ()> {
			&self.peers[i]
		}

		fn peers(&self) -> &Vec<Arc<Peer<Self::Verifier, ()>>> {
			&self.peers
		}

		fn mut_peers<F: Fn(&mut Vec<Arc<Peer<Self::Verifier, ()>>>)>(&mut self, closure: F) {
			closure(&mut self.peers);
		}

		fn started(&self) -> bool {
			self.started
		}

		fn set_started(&mut self, new: bool) {
			self.started = new;
		}
	}

	#[test]
	fn authoring_blocks() {
		::env_logger::init().ok();
		let mut net = AuraTestNet::new(3);

		net.start();

		let peers = &[
			(0, Keyring::Alice),
			(1, Keyring::Bob),
			(2, Keyring::Charlie),
		];

		let net = Arc::new(Mutex::new(net));
		let mut import_notifications = Vec::new();

		let mut runtime = current_thread::Runtime::new().unwrap();
		for (peer_id, key) in peers {
			let mut client = net.lock().peer(*peer_id).client().clone();
			let environ = Arc::new(DummyFactory(client.clone()));
			import_notifications.push(
				client.import_notification_stream()
					.take_while(|n| {
						Ok(!(n.origin != BlockOrigin::Own && n.header.number() < &5))
					})
					.for_each(move |_| Ok(()))
			);

			let slot_duration = SlotDuration::get_or_compute(&*client)
				.expect("slot duration available");

			let aura = start_aura(
				slot_duration,
				Arc::new(key.clone().into()),
				client.clone(),
				client,
				environ.clone(),
				DummyOracle,
				futures::empty(),
			);

			runtime.spawn(aura);
		}

		// wait for all finalized on each.
		let wait_for = ::futures::future::join_all(import_notifications)
			.map(|_| ())
			.map_err(|_| ());

		let drive_to_completion = ::tokio::timer::Interval::new_interval(TEST_ROUTING_INTERVAL)
			.for_each(move |_| {
				net.lock().send_import_notifications();
				net.lock().sync();
				Ok(())
			})
			.map(|_| ())
			.map_err(|_| ());

		runtime.block_on(wait_for.select(drive_to_completion).map_err(|_| ())).unwrap();
	}
}
