// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Collation node logic.
//!
//! A collator node lives on a distinct parachain and submits a proposal for
//! a state transition, along with a proof for its validity
//! (what we might call a witness or block data).
//!
//! One of collators' other roles is to route messages between chains.
//! Each parachain produces a list of "egress" posts of messages for each other
//! parachain on each block, for a total of N^2 lists all together.
//!
//! We will refer to the egress list at relay chain block X of parachain A with
//! destination B as egress(X)[A -> B]
//!
//! On every block, each parachain will be intended to route messages from some
//! subset of all the other parachains. (NOTE: in practice this is not done until PoC-3)
//!
//! Since the egress information is unique to every block, when routing from a
//! parachain a collator must gather all egress posts from that parachain
//! up to the last point in history that messages were successfully routed
//! from that parachain, accounting for relay chain blocks where no candidate
//! from the collator's parachain was produced.
//!
//! In the case that all parachains route to each other and a candidate for the
//! collator's parachain was included in the last relay chain block, the collator
//! only has to gather egress posts from other parachains one block back in relay
//! chain history.
//!
//! This crate defines traits which provide context necessary for collation logic
//! to be performed, as the collation logic itself.

extern crate futures;
extern crate substrate_client as client;
extern crate substrate_codec as codec;
extern crate substrate_primitives as primitives;
extern crate ed25519;
extern crate tokio;

extern crate polkadot_api;
extern crate polkadot_cli;
extern crate polkadot_runtime;
extern crate polkadot_primitives;

#[macro_use]
extern crate log;

use std::collections::{BTreeSet, BTreeMap, HashSet};
use std::fmt;
use std::sync::Arc;
use std::time::{Duration, Instant};

use futures::{future, stream, Stream, Future, IntoFuture};
use client::BlockchainEvents;
use polkadot_api::PolkadotApi;
use polkadot_primitives::{AccountId, BlockId, SessionKey};
use polkadot_primitives::parachain::{self, BlockData, DutyRoster, HeadData, ConsolidatedIngress, Message, Id as ParaId};
use polkadot_cli::{ServiceComponents, Service, CustomConfiguration};
use polkadot_cli::{Worker, IntoExit};
use tokio::timer::Deadline;

pub use polkadot_cli::VersionInfo;

const COLLATION_TIMEOUT: Duration = Duration::from_secs(30);

/// Error to return when the head data was invalid.
#[derive(Clone, Copy, Debug)]
pub struct InvalidHead;

/// Collation errors.
#[derive(Debug)]
pub enum Error<R> {
	/// Error on the relay-chain side of things.
	Polkadot(R),
	/// Error on the collator side of things.
	Collator(InvalidHead),
}

impl<R: fmt::Display> fmt::Display for Error<R> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			Error::Polkadot(ref err) => write!(f, "Polkadot node error: {}", err),
			Error::Collator(_) => write!(f, "Collator node error: Invalid head data"),
		}
	}
}

/// Parachain context needed for collation.
///
/// This can be implemented through an externally attached service or a stub.
/// This is expected to be a lightweight, shared type like an Arc.
pub trait ParachainContext: Clone {
	/// Produce a candidate, given the latest ingress queue information and the last parachain head.
	fn produce_candidate<I: IntoIterator<Item=(ParaId, Message)>>(
		&self,
		last_head: HeadData,
		ingress: I,
	) -> Result<(BlockData, HeadData), InvalidHead>;
}

/// Relay chain context needed to collate.
/// This encapsulates a network and local database which may store
/// some of the input.
pub trait RelayChainContext {
	type Error;

	/// Future that resolves to the un-routed egress queues of a parachain.
	/// The first item is the oldest.
	type FutureEgress: IntoFuture<Item=Vec<Vec<Message>>, Error=Self::Error>;

	/// Provide a set of all parachains meant to be routed to at a block.
	fn routing_parachains(&self) -> BTreeSet<ParaId>;

	/// Get un-routed egress queues from a parachain to the local parachain.
	fn unrouted_egress(&self, id: ParaId) -> Self::FutureEgress;
}

fn key_to_account_id(key: &ed25519::Pair) -> AccountId {
	let pubkey_bytes: [u8; 32] = key.public().into();
	pubkey_bytes.into()
}

/// Collate the necessary ingress queue using the given context.
pub fn collate_ingress<'a, R>(relay_context: R)
	-> impl Future<Item=ConsolidatedIngress, Error=R::Error> + 'a
	where
		R: RelayChainContext,
		R::Error: 'a,
		R::FutureEgress: 'a,
{
	let mut egress_fetch = Vec::new();

	for routing_parachain in relay_context.routing_parachains() {
		let fetch = relay_context
			.unrouted_egress(routing_parachain)
			.into_future()
			.map(move |egresses| (routing_parachain, egresses));

		egress_fetch.push(fetch);
	}

	// create a map ordered first by the depth of the egress queue
	// and then by the parachain ID.
	//
	// then transform that into the consolidated egress queue.
	stream::futures_unordered(egress_fetch)
		.fold(BTreeMap::new(), |mut map, (routing_id, egresses)| {
			for (depth, egress) in egresses.into_iter().rev().enumerate() {
				let depth = -(depth as i64);
				map.insert((depth, routing_id), egress);
			}

			Ok(map)
		})
		.map(|ordered| ordered.into_iter().map(|((_, id), egress)| (id, egress)))
		.map(|i| i.collect::<Vec<_>>())
		.map(ConsolidatedIngress)
}

/// Produce a candidate for the parachain, with given contexts, parent head, and signing key.
pub fn collate<'a, R, P>(
	local_id: ParaId,
	last_head: HeadData,
	relay_context: R,
	para_context: P,
	key: Arc<ed25519::Pair>,
)
	-> impl Future<Item=parachain::Collation, Error=Error<R::Error>> + 'a
	where
		R: RelayChainContext + 'a,
		R::Error: 'a,
		R::FutureEgress: 'a,
		P: ParachainContext + 'a,
{
	collate_ingress(relay_context).map_err(Error::Polkadot).and_then(move |ingress| {
		let (block_data, head_data) = para_context.produce_candidate(
			last_head,
			ingress.0.iter().flat_map(|&(id, ref msgs)| msgs.iter().cloned().map(move |msg| (id, msg)))
		).map_err(Error::Collator)?;

		let block_data_hash = block_data.hash();
		let signature = key.sign(&block_data_hash.0[..]).into();

		let receipt = parachain::CandidateReceipt {
			parachain_index: local_id,
			collator: key_to_account_id(&*key),
			signature,
			head_data,
			balance_uploads: Vec::new(),
			egress_queue_roots: Vec::new(),
			fees: 0,
			block_data_hash,
		};

		Ok(parachain::Collation {
			receipt,
			block_data,
		})
	})
}

/// Polkadot-api context.
struct ApiContext;

impl RelayChainContext for ApiContext {
	type Error = ::polkadot_api::Error;
	type FutureEgress = Result<Vec<Vec<Message>>, Self::Error>;

	fn routing_parachains(&self) -> BTreeSet<ParaId> {
		BTreeSet::new()
	}

	fn unrouted_egress(&self, _id: ParaId) -> Self::FutureEgress {
		Ok(Vec::new())
	}
}

struct CollationNode<P, E> {
	parachain_context: P,
	exit: E,
	para_id: ParaId,
	key: Arc<ed25519::Pair>,
}

impl<P, E> IntoExit for CollationNode<P, E> where
	P: ParachainContext + Send + 'static,
	E: Future<Item=(),Error=()> + Send + 'static
{
	type Exit = E;
	fn into_exit(self) -> Self::Exit {
		self.exit
	}
}

impl<P, E> Worker for CollationNode<P, E> where
	P: ParachainContext + Send + 'static,
	E: Future<Item=(),Error=()> + Send + 'static
{
	type Work = Box<Future<Item=(),Error=()> + Send>;

	fn configuration(&self) -> CustomConfiguration {
		let mut config = CustomConfiguration::default();
		config.collating_for = Some((
			key_to_account_id(&*self.key),
			self.para_id.clone(),
		));
		config
	}

	fn work<C: ServiceComponents>(self, service: &Service<C>) -> Self::Work {
		let CollationNode { parachain_context, exit, para_id, key } = self;
		let client = service.client();
		let api = service.api();
		let network = service.network();

		let work = client.import_notification_stream()
			.for_each(move |notification| {
				macro_rules! try_fr {
					($e:expr) => {
						match $e {
							Ok(x) => x,
							Err(e) => return future::Either::A(future::err(Error::Polkadot(e))),
						}
					}
				}

				let relay_parent = notification.hash;
				let id = BlockId::hash(relay_parent);

				let network = network.clone();
				let api = api.clone();
				let key = key.clone();
				let parachain_context = parachain_context.clone();

				let work = future::lazy(move || {
					let last_head = match try_fr!(api.parachain_head(&id, para_id)) {
						Some(last_head) => last_head,
						None => return future::Either::A(future::ok(())),
					};

					let targets = compute_targets(
						para_id,
						try_fr!(api.session_keys(&id)).as_slice(),
						try_fr!(api.duty_roster(&id)),
					);

					let collation_work = collate(
						para_id,
						HeadData(last_head),
						ApiContext,
						parachain_context,
						key,
					).map(move |collation| {
						network.with_spec(|spec, ctx| spec.add_local_collation(
							ctx,
							relay_parent,
							targets,
							collation,
						));
					});

					future::Either::B(collation_work)
				});
				let deadlined = Deadline::new(work, Instant::now() + COLLATION_TIMEOUT);
				let silenced = deadlined.then(|res| match res {
					Ok(()) => Ok(()),
					Err(e) => {
						warn!("Collation failure: {}", e);
						Ok(())
					}
				});

				tokio::spawn(silenced);
				Ok(())
			});

		let work_and_exit = work.select(exit).then(|_| Ok(()));
		Box::new(work_and_exit) as Box<_>
	}
}

fn compute_targets(para_id: ParaId, session_keys: &[SessionKey], roster: DutyRoster) -> HashSet<SessionKey> {
	use polkadot_primitives::parachain::Chain;

	roster.validator_duty.iter().enumerate()
		.filter(|&(_, c)| c == &Chain::Parachain(para_id))
		.filter_map(|(i, _)| session_keys.get(i))
		.cloned()
		.collect()
}

/// Run a collator node with the given `RelayChainContext` and `ParachainContext` and
/// arguments to the underlying polkadot node.
///
/// Provide a future which resolves when the node should exit.
/// This function blocks until done.
pub fn run_collator<P, E, I, ArgT>(
	parachain_context: P,
	para_id: ParaId,
	exit: E,
	key: Arc<ed25519::Pair>,
	args: I,
	version: VersionInfo,
) -> polkadot_cli::error::Result<()> where
	P: ParachainContext + Send + 'static,
	E: IntoFuture<Item=(),Error=()>,
	E::Future: Send + Clone + 'static,
	I: IntoIterator<Item=ArgT>,
	ArgT: Into<std::ffi::OsString> + Clone,
{
	let node_logic = CollationNode { parachain_context, exit: exit.into_future(), para_id, key };
	polkadot_cli::run(args, node_logic, version)
}

#[cfg(test)]
mod tests {
	use super::*;

	use std::collections::{HashMap, BTreeSet};

	use futures::Future;
	use polkadot_primitives::parachain::{Message, Id as ParaId};

	pub struct DummyRelayChainCtx {
		egresses: HashMap<ParaId, Vec<Vec<Message>>>,
		currently_routing: BTreeSet<ParaId>,
	}

	impl RelayChainContext for DummyRelayChainCtx {
		type Error = ();
		type FutureEgress = Result<Vec<Vec<Message>>, ()>;

		fn routing_parachains(&self) -> BTreeSet<ParaId> {
			self.currently_routing.clone()
		}

		fn unrouted_egress(&self, id: ParaId) -> Result<Vec<Vec<Message>>, ()> {
			Ok(self.egresses.get(&id).cloned().unwrap_or_default())
		}
	}

	#[test]
	fn collates_ingress() {
		let route_from = |x: &[ParaId]| {
			 let mut set = BTreeSet::new();
			 set.extend(x.iter().cloned());
			 set
		};

		let message = |x: Vec<u8>| vec![Message(x)];

		let dummy_ctx = DummyRelayChainCtx {
			currently_routing: route_from(&[2.into(), 3.into()]),
			egresses: vec![
				// egresses for `2`: last routed successfully 5 blocks ago.
				(2.into(), vec![
					message(vec![1, 2, 3]),
					message(vec![4, 5, 6]),
					message(vec![7, 8]),
					message(vec![10]),
					message(vec![12]),
				]),

				// egresses for `3`: last routed successfully 3 blocks ago.
				(3.into(), vec![
					message(vec![9]),
					message(vec![11]),
					message(vec![13]),
				]),
			].into_iter().collect(),
		};

		assert_eq!(
			collate_ingress(dummy_ctx).wait().unwrap(),
			ConsolidatedIngress(vec![
				(2.into(), message(vec![1, 2, 3])),
				(2.into(), message(vec![4, 5, 6])),
				(2.into(), message(vec![7, 8])),
				(3.into(), message(vec![9])),
				(2.into(), message(vec![10])),
				(3.into(), message(vec![11])),
				(2.into(), message(vec![12])),
				(3.into(), message(vec![13])),
			]
		))
	}
}
