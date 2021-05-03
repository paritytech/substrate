// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
// Copyright (C) 2021 Subspace Labs, Inc.
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

//! RPC api for PoC.

use futures::channel::mpsc::UnboundedSender;
use futures::future;
use futures::future::Either;
use futures::{FutureExt as _, SinkExt, StreamExt, TryFutureExt as _, TryStreamExt};
use jsonrpc_core::{
    futures::future as rpc_future,
    futures::{future::Executor as Executor01, future::Future as Future01, Sink, Stream},
    Error as RpcError, Result as RpcResult,
};
use jsonrpc_derive::rpc;
use jsonrpc_pubsub::{manager::SubscriptionManager, typed::Subscriber, SubscriptionId};
use log::{debug, warn};
use parking_lot::Mutex;
use sc_consensus_poc::{NewSlotInfo, NewSlotNotifier};
use serde::{Deserialize, Serialize};
use sp_consensus_poc::digests::Solution;
use sp_consensus_poc::FarmerId;
use sp_core::crypto::Public;
use std::sync::mpsc;
use std::time::Duration;
use std::{collections::HashMap, sync::Arc};

const SOLUTION_TIMEOUT: Duration = Duration::from_secs(5);

type Slot = u64;
type FutureResult<T> = Box<dyn rpc_future::Future<Item = T, Error = RpcError> + Send>;

// TODO: Re-evaluate if we can share this with farmer
/// Information about new slot that just arrived
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RpcNewSlotInfo {
    /// Slot number
    pub slot_number: Slot,
    /// Slot challenge
    pub challenge: [u8; 8],
    /// Acceptable solution range
    pub solution_range: u64,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct RpcSolution {
    pub public_key: [u8; 32],
    pub nonce: u64,
    pub encoding: Vec<u8>,
    pub signature: Vec<u8>,
    pub tag: [u8; 8],
}

#[derive(Debug, Serialize, Deserialize)]
pub struct ProposedProofOfSpaceResult {
    pub slot_number: Slot,
    pub solution: Option<RpcSolution>,
}

/// Provides rpc methods for interacting with PoC.
#[rpc]
pub trait PoCApi {
    /// RPC metadata
    type Metadata;

    #[rpc(name = "poc_proposeProofOfSpace")]
    fn propose_proof_of_space(
        &self,
        proposed_proof_of_space_result: ProposedProofOfSpaceResult,
    ) -> FutureResult<()>;

    /// Slot info subscription
    #[pubsub(
        subscription = "poc_slot_info",
        subscribe,
        name = "poc_subscribeSlotInfo"
    )]
    fn subscribe_slot_info(&self, metadata: Self::Metadata, subscriber: Subscriber<RpcNewSlotInfo>);

    /// Unsubscribe from slot info subscription.
    #[pubsub(
        subscription = "poc_slot_info",
        unsubscribe,
        name = "poc_unsubscribeSlotInfo"
    )]
    fn unsubscribe_slot_info(
        &self,
        metadata: Option<Self::Metadata>,
        id: SubscriptionId,
    ) -> RpcResult<bool>;
}

/// Implements the PoCRpc trait for interacting with PoC.
pub struct PoCRpcHandler {
    manager: SubscriptionManager,
    notification_senders: Arc<Mutex<Vec<UnboundedSender<RpcNewSlotInfo>>>>,
    solution_senders:
        Arc<Mutex<HashMap<Slot, futures::channel::mpsc::Sender<Option<RpcSolution>>>>>,
}

/// PoCRpcHandler is used for notifying subscribers about arrival of new slots and for submission of
/// solutions (or lack thereof).
///
/// Internally every time slot notifier emits information about new slot, notification is sent to
/// every subscriber, after which RPC server waits for the same number of `poc_proposeProofOfSpace`
/// requests with `Option<RpcSolution>` in them or until timeout is exceeded. The first valid
/// solution for a particular slot wins, others are ignored.
impl PoCRpcHandler {
    /// Creates a new instance of the PoCRpc handler.
    pub fn new<E>(executor: E, new_slot_notifier: NewSlotNotifier) -> Self
    where
        E: Executor01<Box<dyn Future01<Item = (), Error = ()> + Send>> + Send + Sync + 'static,
    {
        let notification_senders: Arc<Mutex<Vec<UnboundedSender<RpcNewSlotInfo>>>> = Arc::default();
        let solution_senders: Arc<
            Mutex<HashMap<Slot, futures::channel::mpsc::Sender<Option<RpcSolution>>>>,
        > = Arc::default();
        std::thread::Builder::new()
            .name("poc_rpc_nsn_handler".to_string())
            .spawn({
                let notification_senders = Arc::clone(&notification_senders);
                let solution_senders = Arc::clone(&solution_senders);
                let new_slot_notifier: std::sync::mpsc::Receiver<(
                    NewSlotInfo,
                    mpsc::SyncSender<Option<Solution>>,
                )> = new_slot_notifier();

                move || {
                    // `new_slot_notifier` receives messages with a tuple containing slot info and
                    // sender for solution.
                    //
                    // We then send slot info to all subscribers and wait for their solutions. As
                    // soon as solution is found we send it back and ignore any other solutions for
                    // that slot.
                    while let Ok((new_slot_info, sync_solution_sender)) = new_slot_notifier.recv() {
                        futures::executor::block_on(async {
                            let (solution_sender, mut solution_receiver) =
                                futures::channel::mpsc::channel(0);
                            solution_senders
                                .lock()
                                .insert(new_slot_info.slot.into(), solution_sender);
                            let mut expected_solutions_count;
                            {
                                let mut notification_senders = notification_senders.lock();
                                expected_solutions_count = notification_senders.len();
                                if expected_solutions_count == 0 {
                                    let _ = sync_solution_sender.send(None);
                                    return;
                                }
                                for notification_sender in notification_senders.iter_mut() {
                                    if notification_sender
                                        .send(RpcNewSlotInfo {
                                            slot_number: new_slot_info.slot.into(),
                                            challenge: new_slot_info.challenge,
                                            solution_range: new_slot_info.solution_range,
                                        })
                                        .await
                                        .is_err()
                                    {
                                        expected_solutions_count -= 1;
                                    }
                                }
                            }

                            let timeout = futures_timer::Delay::new(SOLUTION_TIMEOUT).map(|_| None);
                            let solution = async move {
                                // TODO: This doesn't track what client sent a solution, allowing
                                //  some clients to send multiple
                                let mut potential_solutions_left = expected_solutions_count;
                                while let Some(solution) = solution_receiver.next().await {
                                    if let Some(solution) = solution {
                                        return Some(Solution {
                                            public_key: FarmerId::from_slice(&solution.public_key),
                                            nonce: solution.nonce,
                                            encoding: solution.encoding,
                                            signature: solution.signature,
                                            tag: solution.tag,
                                        });
                                    }
                                    potential_solutions_left -= 1;
                                    if potential_solutions_left == 0 {
                                        break;
                                    }
                                }

                                return None;
                            };

                            let solution = match future::select(timeout, Box::pin(solution)).await {
                                Either::Left((value1, _)) => value1,
                                Either::Right((value2, _)) => value2,
                            };

                            if let Err(error) = sync_solution_sender.send(solution) {
                                debug!("Failed to send solution: {}", error);
                            }

                            solution_senders.lock().remove(&new_slot_info.slot.into());
                        });
                    }
                }
            })
            .expect("Failed to spawn poc rpc new slot notifier handler");
        let manager = SubscriptionManager::new(Arc::new(executor));
        Self {
            manager,
            notification_senders,
            solution_senders,
        }
    }
}

impl PoCApi for PoCRpcHandler {
    type Metadata = sc_rpc_api::Metadata;

    fn propose_proof_of_space(
        &self,
        proposed_proof_of_space_result: ProposedProofOfSpaceResult,
    ) -> FutureResult<()> {
        let sender = self
            .solution_senders
            .lock()
            .get(&proposed_proof_of_space_result.slot_number)
            .cloned();
        let future = async move {
            if let Some(mut sender) = sender {
                let _ = sender.send(proposed_proof_of_space_result.solution).await;
            }

            Ok(())
        }
        .boxed();
        Box::new(future.compat())
    }

    fn subscribe_slot_info(
        &self,
        _metadata: Self::Metadata,
        subscriber: Subscriber<RpcNewSlotInfo>,
    ) {
        self.manager.add(subscriber, |sink| {
            let (tx, rx) = futures::channel::mpsc::unbounded();
            self.notification_senders.lock().push(tx);
            sink.sink_map_err(|e| warn!("Error sending notifications: {:?}", e))
                .send_all(rx.map(Ok::<_, ()>).compat().map(|res| Ok(res)))
                .map(|_| ())
        });
    }

    fn unsubscribe_slot_info(
        &self,
        _metadata: Option<Self::Metadata>,
        id: SubscriptionId,
    ) -> RpcResult<bool> {
        Ok(self.manager.cancel(id))
    }
}
