// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use futures::channel::oneshot;
use parking_lot::Mutex;
use sc_client_api::Backend;
use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use sp_runtime::traits::Block as BlockT;
use std::{
	collections::{hash_map::Entry, HashMap},
	sync::{atomic::AtomicBool, Arc},
	time::{Duration, Instant},
};

use crate::chain_head::{subscription::SubscriptionManagementError, FollowEvent};

/// The queue size after which the `sc_utils::mpsc::tracing_unbounded` would produce warnings.
const QUEUE_SIZE_WARNING: usize = 512;

/// The state machine of a block of a single subscription ID.
///
/// # Motivation
///
/// Each block is registered twice: once from the `BestBlock` event
/// and once from the `Finalized` event.
///
/// The state of a block must be tracked until both events register the
/// block and the user calls `unpin`.
///
/// Otherwise, the following race might happen:
///  T0. BestBlock event: hash is tracked and pinned in backend.
///  T1. User calls unpin: hash is untracked and unpinned in backend.
///  T2. Finalized event: hash is tracked (no previous history) and pinned again.
///
/// # State Machine Transition
///
/// ```ignore
///                   (register)
/// [ REGISTERED ]  ---------------> [ FULLY REGISTERED ]
///       |                              |
///       | (unpin)                      | (unpin)
///       |                              |
///       V           (register)         V
/// [ UNPINNED ]  -----------------> [ FULLY UNPINNED ]
/// ```
#[derive(Debug, Clone, PartialEq)]
enum BlockStateMachine {
	/// The block was registered by one event (either `Finalized` or `BestBlock` event).
	///
	/// Unpin was not called.
	Registered,
	/// The block was registered by both events (`Finalized` and `BestBlock` events).
	///
	/// Unpin was not called.
	FullyRegistered,
	/// The block was registered by one event (either `Finalized` or `BestBlock` event),
	///
	/// Unpin __was__ called.
	Unpinned,
	/// The block was registered by both events (`Finalized` and `BestBlock` events).
	///
	/// Unpin __was__ called.
	FullyUnpinned,
}

impl BlockStateMachine {
	fn new() -> Self {
		BlockStateMachine::Registered
	}

	fn advance_register(&mut self) {
		match self {
			BlockStateMachine::Registered => *self = BlockStateMachine::FullyRegistered,
			BlockStateMachine::Unpinned => *self = BlockStateMachine::FullyUnpinned,
			_ => (),
		}
	}

	fn advance_unpin(&mut self) {
		match self {
			BlockStateMachine::Registered => *self = BlockStateMachine::Unpinned,
			BlockStateMachine::FullyRegistered => *self = BlockStateMachine::FullyUnpinned,
			_ => (),
		}
	}

	fn was_unpinned(&self) -> bool {
		match self {
			BlockStateMachine::Unpinned => true,
			BlockStateMachine::FullyUnpinned => true,
			_ => false,
		}
	}
}

/// Limit the number of ongoing operations across methods.
struct LimitOperations {
	/// Limit the number of ongoing operations for this subscription.
	semaphore: Arc<tokio::sync::Semaphore>,
}

impl LimitOperations {
	/// Constructs a new [`LimitOperations`].
	fn new(max_operations: usize) -> Self {
		LimitOperations { semaphore: Arc::new(tokio::sync::Semaphore::new(max_operations)) }
	}

	/// Reserves capacity to execute at least one operation and at most the requested items.
	///
	/// Dropping [`PermitOperations`] without executing an operation will release
	/// the reserved capacity.
	///
	/// Returns nothing if there's no space available, else returns a permit
	/// that guarantees that at least one operation can be executed.
	fn reserve_at_most(&self, to_reserve: usize) -> Option<PermitOperations> {
		let num_ops = std::cmp::min(self.semaphore.available_permits(), to_reserve);

		if num_ops == 0 {
			return None
		}

		let permits = Arc::clone(&self.semaphore)
			.try_acquire_many_owned(num_ops.try_into().ok()?)
			.ok()?;

		Some(PermitOperations { num_ops, _permit: permits })
	}
}

/// Permits a number of operations to be executed.
///
/// [`PermitOperations`] are returned by [`LimitOperations::reserve()`] and are used
/// to guarantee the RPC server can execute the number of operations.
///
/// The number of reserved items are given back to the [`LimitOperations`] on drop.
struct PermitOperations {
	/// The number of operations permitted (reserved).
	num_ops: usize,
	/// The permit for these operations.
	_permit: tokio::sync::OwnedSemaphorePermit,
}

/// The state of one operation.
///
/// This is directly exposed to users via `chain_head_unstable_continue` and
/// `chain_head_unstable_stop_operation`.
#[derive(Clone)]
pub struct OperationState {
	/// The shared operation state that holds information about the
	/// `waitingForContinue` event and cancellation.
	shared_state: Arc<SharedOperationState>,
	/// Send notifications when the user calls `chainHead_continue` method.
	send_continue: tokio::sync::mpsc::Sender<()>,
}

impl OperationState {
	/// Returns true if `chainHead_continue` is called after the
	/// `waitingForContinue` event was emitted for the associated
	/// operation ID.
	pub fn submit_continue(&self) -> bool {
		// `waitingForContinue` not generated.
		if !self.shared_state.requested_continue.load(std::sync::atomic::Ordering::Acquire) {
			return false
		}

		// Has enough capacity for 1 message.
		// Can fail if the `stop_operation` propagated the stop first.
		self.send_continue.try_send(()).is_ok()
	}

	/// Stops the operation if `waitingForContinue` event was emitted for the associated
	/// operation ID.
	///
	/// Returns nothing in accordance with `chainHead_unstable_stopOperation`.
	pub fn stop_operation(&self) {
		// `waitingForContinue` not generated.
		if !self.shared_state.requested_continue.load(std::sync::atomic::Ordering::Acquire) {
			return
		}

		self.shared_state
			.operation_stopped
			.store(true, std::sync::atomic::Ordering::Release);

		// Send might not have enough capacity if `submit_continue` was sent first.
		// However, the `operation_stopped` boolean was set.
		let _ = self.send_continue.try_send(());
	}
}

/// The shared operation state between the backend [`RegisteredOperation`] and frontend
/// [`RegisteredOperation`].
struct SharedOperationState {
	/// True if the `chainHead` generated `waitingForContinue` event.
	requested_continue: AtomicBool,
	/// True if the operation was cancelled by the user.
	operation_stopped: AtomicBool,
}

impl SharedOperationState {
	/// Constructs a new [`SharedOperationState`].
	///
	/// This is efficiently cloned under a single heap allocation.
	fn new() -> Arc<Self> {
		Arc::new(SharedOperationState {
			requested_continue: AtomicBool::new(false),
			operation_stopped: AtomicBool::new(false),
		})
	}
}

/// The registered operation passed to the `chainHead` methods.
///
/// This is used internally by the `chainHead` methods.
pub struct RegisteredOperation {
	/// The shared operation state that holds information about the
	/// `waitingForContinue` event and cancellation.
	shared_state: Arc<SharedOperationState>,
	/// Receive notifications when the user calls `chainHead_continue` method.
	recv_continue: tokio::sync::mpsc::Receiver<()>,
	/// The operation ID of the request.
	operation_id: String,
	/// Track the operations ID of this subscription.
	operations: Arc<Mutex<HashMap<String, OperationState>>>,
	/// Permit a number of items to be executed by this operation.
	permit: PermitOperations,
}

impl RegisteredOperation {
	/// Wait until the user calls `chainHead_continue` or the operation
	/// is cancelled via `chainHead_stopOperation`.
	pub async fn wait_for_continue(&mut self) {
		self.shared_state
			.requested_continue
			.store(true, std::sync::atomic::Ordering::Release);

		// The sender part of this channel is around for as long as this object exists,
		// because it is stored in the `OperationState` of the `operations` field.
		// The sender part is removed from tracking when this object is dropped.
		let _ = self.recv_continue.recv().await;

		self.shared_state
			.requested_continue
			.store(false, std::sync::atomic::Ordering::Release);
	}

	/// Returns true if the current operation was stopped.
	pub fn was_stopped(&self) -> bool {
		self.shared_state.operation_stopped.load(std::sync::atomic::Ordering::Acquire)
	}

	/// Get the operation ID.
	pub fn operation_id(&self) -> String {
		self.operation_id.clone()
	}

	/// Returns the number of reserved elements for this permit.
	///
	/// This can be smaller than the number of items requested via [`LimitOperations::reserve()`].
	pub fn num_reserved(&self) -> usize {
		self.permit.num_ops
	}
}

impl Drop for RegisteredOperation {
	fn drop(&mut self) {
		let mut operations = self.operations.lock();
		operations.remove(&self.operation_id);
	}
}

/// The ongoing operations of a subscription.
struct Operations {
	/// The next operation ID to be generated.
	next_operation_id: usize,
	/// Limit the number of ongoing operations.
	limits: LimitOperations,
	/// Track the operations ID of this subscription.
	operations: Arc<Mutex<HashMap<String, OperationState>>>,
}

impl Operations {
	/// Constructs a new [`Operations`].
	fn new(max_operations: usize) -> Self {
		Operations {
			next_operation_id: 0,
			limits: LimitOperations::new(max_operations),
			operations: Default::default(),
		}
	}

	/// Register a new operation.
	pub fn register_operation(&mut self, to_reserve: usize) -> Option<RegisteredOperation> {
		let permit = self.limits.reserve_at_most(to_reserve)?;

		let operation_id = self.next_operation_id();

		// At most one message can be sent.
		let (send_continue, recv_continue) = tokio::sync::mpsc::channel(1);
		let shared_state = SharedOperationState::new();

		let state = OperationState { send_continue, shared_state: shared_state.clone() };

		// Cloned operations for removing the current ID on drop.
		let operations = self.operations.clone();
		operations.lock().insert(operation_id.clone(), state);

		Some(RegisteredOperation { shared_state, operation_id, recv_continue, operations, permit })
	}

	/// Get the associated operation state with the ID.
	pub fn get_operation(&self, id: &str) -> Option<OperationState> {
		self.operations.lock().get(id).map(|state| state.clone())
	}

	/// Generate the next operation ID for this subscription.
	fn next_operation_id(&mut self) -> String {
		let op_id = self.next_operation_id;
		self.next_operation_id += 1;
		op_id.to_string()
	}
}

struct BlockState {
	/// The state machine of this block.
	state_machine: BlockStateMachine,
	/// The timestamp when the block was inserted.
	timestamp: Instant,
}

/// The state of a single subscription ID.
struct SubscriptionState<Block: BlockT> {
	/// The `with_runtime` parameter flag of the subscription.
	with_runtime: bool,
	/// Signals the "Stop" event.
	tx_stop: Option<oneshot::Sender<()>>,
	/// The sender of message responses to the `chainHead_follow` events.
	///
	/// This object is cloned between methods.
	response_sender: TracingUnboundedSender<FollowEvent<Block::Hash>>,
	/// The ongoing operations of a subscription.
	operations: Operations,
	/// Track the block hashes available for this subscription.
	///
	/// This implementation assumes:
	/// - most of the time subscriptions keep a few blocks of the chain's head pinned
	/// - iteration through the blocks happens only when the hard limit is exceeded.
	///
	/// Considering the assumption, iterating (in the unlike case) the hashmap O(N) is
	/// more time efficient and code friendly than paying for:
	/// - extra space: an extra BTreeMap<Instant, Hash> to older hashes by oldest insertion
	/// - extra time: O(log(N)) for insert/remove/find each `pin` block time per subscriptions
	blocks: HashMap<Block::Hash, BlockState>,
}

impl<Block: BlockT> SubscriptionState<Block> {
	/// Trigger the stop event for the current subscription.
	///
	/// This can happen on internal failure (ie, the pruning deleted the block from memory)
	/// or if the subscription exceeded the available pinned blocks.
	fn stop(&mut self) {
		if let Some(tx_stop) = self.tx_stop.take() {
			let _ = tx_stop.send(());
		}
	}

	/// Keep track of the given block hash for this subscription.
	///
	/// This does not handle pinning in the backend.
	///
	/// Returns:
	/// - true if this is the first time that the block is registered
	/// - false if the block was already registered
	fn register_block(&mut self, hash: Block::Hash) -> bool {
		match self.blocks.entry(hash) {
			Entry::Occupied(mut occupied) => {
				let block_state = occupied.get_mut();

				block_state.state_machine.advance_register();
				// Block was registered twice and unpin was called.
				if block_state.state_machine == BlockStateMachine::FullyUnpinned {
					occupied.remove();
				}

				// Second time we register this block.
				false
			},
			Entry::Vacant(vacant) => {
				vacant.insert(BlockState {
					state_machine: BlockStateMachine::new(),
					timestamp: Instant::now(),
				});

				// First time we register this block.
				true
			},
		}
	}

	/// A block is unregistered when the user calls `unpin`.
	///
	/// Returns:
	/// - true if the block can be unpinned.
	/// - false if the subscription does not contain the block or it was unpinned.
	fn unregister_block(&mut self, hash: Block::Hash) -> bool {
		match self.blocks.entry(hash) {
			Entry::Occupied(mut occupied) => {
				let block_state = occupied.get_mut();

				// Cannot unpin a block twice.
				if block_state.state_machine.was_unpinned() {
					return false
				}

				block_state.state_machine.advance_unpin();
				// Block was registered twice and unpin was called.
				if block_state.state_machine == BlockStateMachine::FullyUnpinned {
					occupied.remove();
				}

				true
			},
			// Block was not tracked.
			Entry::Vacant(_) => false,
		}
	}

	/// A subscription contains a block when the block was
	/// registered (`pin` was called) and the block was not `unpinned` yet.
	///
	/// Returns `true` if the subscription contains the block.
	fn contains_block(&self, hash: Block::Hash) -> bool {
		let Some(state) = self.blocks.get(&hash) else {
			// Block was not tracked.
			return false
		};

		// Subscription no longer contains the block if `unpin` was called.
		!state.state_machine.was_unpinned()
	}

	/// Get the timestamp of the oldest inserted block.
	///
	/// # Note
	///
	/// This iterates over all the blocks of the subscription.
	fn find_oldest_block_timestamp(&self) -> Instant {
		let mut timestamp = Instant::now();
		for (_, state) in self.blocks.iter() {
			timestamp = std::cmp::min(timestamp, state.timestamp);
		}
		timestamp
	}

	/// Register a new operation.
	///
	/// The registered operation can execute at least one item and at most the requested items.
	fn register_operation(&mut self, to_reserve: usize) -> Option<RegisteredOperation> {
		self.operations.register_operation(to_reserve)
	}

	/// Get the associated operation state with the ID.
	pub fn get_operation(&self, id: &str) -> Option<OperationState> {
		self.operations.get_operation(id)
	}
}

/// Keeps a specific block pinned while the handle is alive.
/// This object ensures that the block is not unpinned while
/// executing an RPC method call.
pub struct BlockGuard<Block: BlockT, BE: Backend<Block>> {
	hash: Block::Hash,
	with_runtime: bool,
	response_sender: TracingUnboundedSender<FollowEvent<Block::Hash>>,
	operation: RegisteredOperation,
	backend: Arc<BE>,
}

// Custom implementation of Debug to avoid bounds on `backend: Debug` for `unwrap_err()` needed for
// testing.
impl<Block: BlockT, BE: Backend<Block>> std::fmt::Debug for BlockGuard<Block, BE> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "BlockGuard hash {:?} with_runtime {:?}", self.hash, self.with_runtime)
	}
}

impl<Block: BlockT, BE: Backend<Block>> BlockGuard<Block, BE> {
	/// Construct a new [`BlockGuard`] .
	fn new(
		hash: Block::Hash,
		with_runtime: bool,
		response_sender: TracingUnboundedSender<FollowEvent<Block::Hash>>,
		operation: RegisteredOperation,
		backend: Arc<BE>,
	) -> Result<Self, SubscriptionManagementError> {
		backend
			.pin_block(hash)
			.map_err(|err| SubscriptionManagementError::Custom(err.to_string()))?;

		Ok(Self { hash, with_runtime, response_sender, operation, backend })
	}

	/// The `with_runtime` flag of the subscription.
	pub fn has_runtime(&self) -> bool {
		self.with_runtime
	}

	/// Send message responses from the `chainHead` methods to `chainHead_follow`.
	pub fn response_sender(&self) -> TracingUnboundedSender<FollowEvent<Block::Hash>> {
		self.response_sender.clone()
	}

	/// Get the details of the registered operation.
	pub fn operation(&mut self) -> &mut RegisteredOperation {
		&mut self.operation
	}
}

impl<Block: BlockT, BE: Backend<Block>> Drop for BlockGuard<Block, BE> {
	fn drop(&mut self) {
		self.backend.unpin_block(self.hash);
	}
}

/// The data propagated back to the `chainHead_follow` method after
/// the subscription is successfully inserted.
pub struct InsertedSubscriptionData<Block: BlockT> {
	/// Signal that the subscription must stop.
	pub rx_stop: oneshot::Receiver<()>,
	/// Receive message responses from the `chainHead` methods.
	pub response_receiver: TracingUnboundedReceiver<FollowEvent<Block::Hash>>,
}

pub struct SubscriptionsInner<Block: BlockT, BE: Backend<Block>> {
	/// Reference count the block hashes across all subscriptions.
	///
	/// The pinned blocks cannot exceed the [`Self::global_limit`] limit.
	/// When the limit is exceeded subscriptions are stopped via the `Stop` event.
	global_blocks: HashMap<Block::Hash, usize>,
	/// The maximum number of pinned blocks across all subscriptions.
	global_max_pinned_blocks: usize,
	/// The maximum duration that a block is allowed to be pinned per subscription.
	local_max_pin_duration: Duration,
	/// The maximum number of ongoing operations per subscription.
	max_ongoing_operations: usize,
	/// Map the subscription ID to internal details of the subscription.
	subs: HashMap<String, SubscriptionState<Block>>,
	/// Backend pinning / unpinning blocks.
	///
	/// The `Arc` is handled one level-above, but substrate exposes the backend as Arc<T>.
	backend: Arc<BE>,
}

impl<Block: BlockT, BE: Backend<Block>> SubscriptionsInner<Block, BE> {
	/// Construct a new [`SubscriptionsInner`] from the specified limits.
	pub fn new(
		global_max_pinned_blocks: usize,
		local_max_pin_duration: Duration,
		max_ongoing_operations: usize,
		backend: Arc<BE>,
	) -> Self {
		SubscriptionsInner {
			global_blocks: Default::default(),
			global_max_pinned_blocks,
			local_max_pin_duration,
			max_ongoing_operations,
			subs: Default::default(),
			backend,
		}
	}

	/// Insert a new subscription ID.
	pub fn insert_subscription(
		&mut self,
		sub_id: String,
		with_runtime: bool,
	) -> Option<InsertedSubscriptionData<Block>> {
		if let Entry::Vacant(entry) = self.subs.entry(sub_id) {
			let (tx_stop, rx_stop) = oneshot::channel();
			let (response_sender, response_receiver) =
				tracing_unbounded("chain-head-method-responses", QUEUE_SIZE_WARNING);
			let state = SubscriptionState::<Block> {
				with_runtime,
				tx_stop: Some(tx_stop),
				response_sender,
				blocks: Default::default(),
				operations: Operations::new(self.max_ongoing_operations),
			};
			entry.insert(state);

			Some(InsertedSubscriptionData { rx_stop, response_receiver })
		} else {
			None
		}
	}

	/// Remove the subscription ID with associated pinned blocks.
	pub fn remove_subscription(&mut self, sub_id: &str) {
		let Some(mut sub) = self.subs.remove(sub_id) else { return };

		// The `Stop` event can be generated only once.
		sub.stop();

		for (hash, state) in sub.blocks.iter() {
			if !state.state_machine.was_unpinned() {
				self.global_unregister_block(*hash);
			}
		}
	}

	/// Ensure that a new block could be pinned.
	///
	/// If the global number of blocks has been reached this method
	/// will remove all subscriptions that have blocks older than the
	/// specified pin duration.
	///
	/// If after removing all subscriptions that exceed the pin duration
	/// there is no space for pinning a new block, then all subscriptions
	/// are terminated.
	///
	/// Returns true if the given subscription is also terminated.
	fn ensure_block_space(&mut self, request_sub_id: &str) -> bool {
		if self.global_blocks.len() < self.global_max_pinned_blocks {
			return false
		}

		// Terminate all subscriptions that have blocks older than
		// the specified pin duration.
		let now = Instant::now();

		let to_remove: Vec<_> = self
			.subs
			.iter_mut()
			.filter_map(|(sub_id, sub)| {
				let sub_time = sub.find_oldest_block_timestamp();
				// Subscriptions older than the specified pin duration should be removed.
				let should_remove = match now.checked_duration_since(sub_time) {
					Some(duration) => duration > self.local_max_pin_duration,
					None => true,
				};
				should_remove.then(|| sub_id.clone())
			})
			.collect();

		let mut is_terminated = false;
		for sub_id in to_remove {
			if sub_id == request_sub_id {
				is_terminated = true;
			}
			self.remove_subscription(&sub_id);
		}

		// Make sure we have enough space after first pass of terminating subscriptions.
		if self.global_blocks.len() < self.global_max_pinned_blocks {
			return is_terminated
		}

		// Sanity check: cannot uphold `chainHead` guarantees anymore. We have not
		// found any subscriptions that have older pinned blocks to terminate.
		let to_remove: Vec<_> = self.subs.keys().map(|sub_id| sub_id.clone()).collect();
		for sub_id in to_remove {
			if sub_id == request_sub_id {
				is_terminated = true;
			}
			self.remove_subscription(&sub_id);
		}
		return is_terminated
	}

	pub fn pin_block(
		&mut self,
		sub_id: &str,
		hash: Block::Hash,
	) -> Result<bool, SubscriptionManagementError> {
		let Some(sub) = self.subs.get_mut(sub_id) else {
			return Err(SubscriptionManagementError::SubscriptionAbsent)
		};

		// Block was already registered for this subscription and therefore
		// globally tracked.
		if !sub.register_block(hash) {
			return Ok(false)
		}

		// Ensure we have enough space only if the hash is not globally registered.
		if !self.global_blocks.contains_key(&hash) {
			// Subscription ID was terminated while ensuring enough space.
			if self.ensure_block_space(sub_id) {
				return Err(SubscriptionManagementError::ExceededLimits)
			}
		}

		self.global_register_block(hash)?;
		Ok(true)
	}

	/// Register the block internally.
	///
	/// If the block is present the reference counter is increased.
	/// If this is a new block, the block is pinned in the backend.
	fn global_register_block(
		&mut self,
		hash: Block::Hash,
	) -> Result<(), SubscriptionManagementError> {
		match self.global_blocks.entry(hash) {
			Entry::Occupied(mut occupied) => {
				*occupied.get_mut() += 1;
			},
			Entry::Vacant(vacant) => {
				self.backend
					.pin_block(hash)
					.map_err(|err| SubscriptionManagementError::Custom(err.to_string()))?;

				vacant.insert(1);
			},
		};
		Ok(())
	}

	/// Unregister the block internally.
	///
	/// If the block is present the reference counter is decreased.
	/// If this is the last reference of the block, the block
	/// is unpinned from the backend and removed from internal tracking.
	fn global_unregister_block(&mut self, hash: Block::Hash) {
		if let Entry::Occupied(mut occupied) = self.global_blocks.entry(hash) {
			let counter = occupied.get_mut();
			if *counter == 1 {
				// Unpin the block from the backend.
				self.backend.unpin_block(hash);
				occupied.remove();
			} else {
				*counter -= 1;
			}
		}
	}

	pub fn unpin_block(
		&mut self,
		sub_id: &str,
		hash: Block::Hash,
	) -> Result<(), SubscriptionManagementError> {
		let Some(sub) = self.subs.get_mut(sub_id) else {
			return Err(SubscriptionManagementError::SubscriptionAbsent)
		};

		// Check that unpin was not called before and the block was pinned
		// for this subscription.
		if !sub.unregister_block(hash) {
			return Err(SubscriptionManagementError::BlockHashAbsent)
		}

		self.global_unregister_block(hash);
		Ok(())
	}

	pub fn lock_block(
		&mut self,
		sub_id: &str,
		hash: Block::Hash,
		to_reserve: usize,
	) -> Result<BlockGuard<Block, BE>, SubscriptionManagementError> {
		let Some(sub) = self.subs.get_mut(sub_id) else {
			return Err(SubscriptionManagementError::SubscriptionAbsent)
		};

		if !sub.contains_block(hash) {
			return Err(SubscriptionManagementError::BlockHashAbsent)
		}

		let Some(operation) = sub.register_operation(to_reserve) else {
			// Error when the server cannot execute at least one operation.
			return Err(SubscriptionManagementError::ExceededLimits)
		};

		BlockGuard::new(
			hash,
			sub.with_runtime,
			sub.response_sender.clone(),
			operation,
			self.backend.clone(),
		)
	}

	pub fn get_operation(&mut self, sub_id: &str, id: &str) -> Option<OperationState> {
		let state = self.subs.get(sub_id)?;
		state.get_operation(id)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sc_block_builder::BlockBuilderProvider;
	use sc_service::client::new_in_mem;
	use sp_consensus::BlockOrigin;
	use sp_core::{testing::TaskExecutor, H256};
	use substrate_test_runtime_client::{
		prelude::*,
		runtime::{Block, RuntimeApi},
		Client, ClientBlockImportExt, GenesisInit,
	};

	/// Maximum number of ongoing operations per subscription ID.
	const MAX_OPERATIONS_PER_SUB: usize = 16;

	fn init_backend() -> (
		Arc<sc_client_api::in_mem::Backend<Block>>,
		Arc<Client<sc_client_api::in_mem::Backend<Block>>>,
	) {
		let backend = Arc::new(sc_client_api::in_mem::Backend::new());
		let executor = substrate_test_runtime_client::new_native_or_wasm_executor();
		let client_config = sc_service::ClientConfig::default();
		let genesis_block_builder = sc_service::GenesisBlockBuilder::new(
			&substrate_test_runtime_client::GenesisParameters::default().genesis_storage(),
			!client_config.no_genesis,
			backend.clone(),
			executor.clone(),
		)
		.unwrap();
		let client = Arc::new(
			new_in_mem::<_, Block, _, RuntimeApi>(
				backend.clone(),
				executor,
				genesis_block_builder,
				None,
				None,
				Box::new(TaskExecutor::new()),
				client_config,
			)
			.unwrap(),
		);
		(backend, client)
	}

	#[test]
	fn block_state_machine_register_unpin() {
		let mut state = BlockStateMachine::new();
		// Starts in `Registered` state.
		assert_eq!(state, BlockStateMachine::Registered);

		state.advance_register();
		assert_eq!(state, BlockStateMachine::FullyRegistered);

		// Can call register multiple times.
		state.advance_register();
		assert_eq!(state, BlockStateMachine::FullyRegistered);

		assert!(!state.was_unpinned());
		state.advance_unpin();
		assert_eq!(state, BlockStateMachine::FullyUnpinned);
		assert!(state.was_unpinned());

		// Can call unpin multiple times.
		state.advance_unpin();
		assert_eq!(state, BlockStateMachine::FullyUnpinned);
		assert!(state.was_unpinned());

		// Nothing to advance.
		state.advance_register();
		assert_eq!(state, BlockStateMachine::FullyUnpinned);
	}

	#[test]
	fn block_state_machine_unpin_register() {
		let mut state = BlockStateMachine::new();
		// Starts in `Registered` state.
		assert_eq!(state, BlockStateMachine::Registered);

		assert!(!state.was_unpinned());
		state.advance_unpin();
		assert_eq!(state, BlockStateMachine::Unpinned);
		assert!(state.was_unpinned());

		// Can call unpin multiple times.
		state.advance_unpin();
		assert_eq!(state, BlockStateMachine::Unpinned);
		assert!(state.was_unpinned());

		state.advance_register();
		assert_eq!(state, BlockStateMachine::FullyUnpinned);
		assert!(state.was_unpinned());

		// Nothing to advance.
		state.advance_register();
		assert_eq!(state, BlockStateMachine::FullyUnpinned);
		// Nothing to unpin.
		state.advance_unpin();
		assert_eq!(state, BlockStateMachine::FullyUnpinned);
		assert!(state.was_unpinned());
	}

	#[test]
	fn sub_state_register_twice() {
		let (response_sender, _response_receiver) =
			tracing_unbounded("test-chain-head-method-responses", QUEUE_SIZE_WARNING);
		let mut sub_state = SubscriptionState::<Block> {
			with_runtime: false,
			tx_stop: None,
			response_sender,
			operations: Operations::new(MAX_OPERATIONS_PER_SUB),
			blocks: Default::default(),
		};

		let hash = H256::random();
		assert_eq!(sub_state.register_block(hash), true);
		let block_state = sub_state.blocks.get(&hash).unwrap();
		// Did not call `register_block` twice.
		assert_eq!(block_state.state_machine, BlockStateMachine::Registered);

		assert_eq!(sub_state.register_block(hash), false);
		let block_state = sub_state.blocks.get(&hash).unwrap();
		assert_eq!(block_state.state_machine, BlockStateMachine::FullyRegistered);

		// Block is no longer tracked when: `register_block` is called twice and
		// `unregister_block` is called once.
		assert_eq!(sub_state.unregister_block(hash), true);
		let block_state = sub_state.blocks.get(&hash);
		assert!(block_state.is_none());
	}

	#[test]
	fn sub_state_register_unregister() {
		let (response_sender, _response_receiver) =
			tracing_unbounded("test-chain-head-method-responses", QUEUE_SIZE_WARNING);
		let mut sub_state = SubscriptionState::<Block> {
			with_runtime: false,
			tx_stop: None,
			response_sender,
			blocks: Default::default(),
			operations: Operations::new(MAX_OPERATIONS_PER_SUB),
		};

		let hash = H256::random();
		// Block was not registered before.
		assert_eq!(sub_state.unregister_block(hash), false);

		assert_eq!(sub_state.register_block(hash), true);
		let block_state = sub_state.blocks.get(&hash).unwrap();
		// Did not call `register_block` twice.
		assert_eq!(block_state.state_machine, BlockStateMachine::Registered);

		// Unregister block before the second `register_block`.
		assert_eq!(sub_state.unregister_block(hash), true);
		let block_state = sub_state.blocks.get(&hash).unwrap();
		assert_eq!(block_state.state_machine, BlockStateMachine::Unpinned);

		assert_eq!(sub_state.register_block(hash), false);
		let block_state = sub_state.blocks.get(&hash);
		assert!(block_state.is_none());

		// Block is no longer tracked when: `register_block` is called twice and
		// `unregister_block` is called once.
		assert_eq!(sub_state.unregister_block(hash), false);
		let block_state = sub_state.blocks.get(&hash);
		assert!(block_state.is_none());
	}

	#[test]
	fn subscription_lock_block() {
		let builder = TestClientBuilder::new();
		let backend = builder.backend();
		let mut subs =
			SubscriptionsInner::new(10, Duration::from_secs(10), MAX_OPERATIONS_PER_SUB, backend);

		let id = "abc".to_string();
		let hash = H256::random();

		// Subscription not inserted.
		let err = subs.lock_block(&id, hash, 1).unwrap_err();
		assert_eq!(err, SubscriptionManagementError::SubscriptionAbsent);

		let _stop = subs.insert_subscription(id.clone(), true).unwrap();
		// Cannot insert the same subscription ID twice.
		assert!(subs.insert_subscription(id.clone(), true).is_none());

		// No block hash.
		let err = subs.lock_block(&id, hash, 1).unwrap_err();
		assert_eq!(err, SubscriptionManagementError::BlockHashAbsent);

		subs.remove_subscription(&id);

		// No subscription.
		let err = subs.lock_block(&id, hash, 1).unwrap_err();
		assert_eq!(err, SubscriptionManagementError::SubscriptionAbsent);
	}

	#[test]
	fn subscription_check_block() {
		let (backend, mut client) = init_backend();

		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash = block.header.hash();
		futures::executor::block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();

		let mut subs =
			SubscriptionsInner::new(10, Duration::from_secs(10), MAX_OPERATIONS_PER_SUB, backend);
		let id = "abc".to_string();

		let _stop = subs.insert_subscription(id.clone(), true).unwrap();

		// First time we are pinning the block.
		assert_eq!(subs.pin_block(&id, hash).unwrap(), true);

		let block = subs.lock_block(&id, hash, 1).unwrap();
		// Subscription started with runtime updates
		assert_eq!(block.has_runtime(), true);

		let invalid_id = "abc-invalid".to_string();
		let err = subs.unpin_block(&invalid_id, hash).unwrap_err();
		assert_eq!(err, SubscriptionManagementError::SubscriptionAbsent);

		// Unpin the block.
		subs.unpin_block(&id, hash).unwrap();
		let err = subs.lock_block(&id, hash, 1).unwrap_err();
		assert_eq!(err, SubscriptionManagementError::BlockHashAbsent);
	}

	#[test]
	fn subscription_ref_count() {
		let (backend, mut client) = init_backend();
		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash = block.header.hash();
		futures::executor::block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();

		let mut subs =
			SubscriptionsInner::new(10, Duration::from_secs(10), MAX_OPERATIONS_PER_SUB, backend);
		let id = "abc".to_string();

		let _stop = subs.insert_subscription(id.clone(), true).unwrap();
		assert_eq!(subs.pin_block(&id, hash).unwrap(), true);
		// Check the global ref count.
		assert_eq!(*subs.global_blocks.get(&hash).unwrap(), 1);
		// Ensure the block propagated to the subscription.
		subs.subs.get(&id).unwrap().blocks.get(&hash).unwrap();

		// Insert the block for the same subscription again (simulate NewBlock + Finalized pinning)
		assert_eq!(subs.pin_block(&id, hash).unwrap(), false);
		// Check the global ref count should not get incremented.
		assert_eq!(*subs.global_blocks.get(&hash).unwrap(), 1);

		// Ensure the hash propagates for the second subscription.
		let id_second = "abcd".to_string();
		let _stop = subs.insert_subscription(id_second.clone(), true).unwrap();
		assert_eq!(subs.pin_block(&id_second, hash).unwrap(), true);
		// Check the global ref count.
		assert_eq!(*subs.global_blocks.get(&hash).unwrap(), 2);
		// Ensure the block propagated to the subscription.
		subs.subs.get(&id_second).unwrap().blocks.get(&hash).unwrap();

		subs.unpin_block(&id, hash).unwrap();
		assert_eq!(*subs.global_blocks.get(&hash).unwrap(), 1);
		// Cannot unpin a block twice for the same subscription.
		let err = subs.unpin_block(&id, hash).unwrap_err();
		assert_eq!(err, SubscriptionManagementError::BlockHashAbsent);

		subs.unpin_block(&id_second, hash).unwrap();
		// Block unregistered from the memory.
		assert!(subs.global_blocks.get(&hash).is_none());
	}

	#[test]
	fn subscription_remove_subscription() {
		let (backend, mut client) = init_backend();
		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash_1 = block.header.hash();
		futures::executor::block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();
		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash_2 = block.header.hash();
		futures::executor::block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();
		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash_3 = block.header.hash();
		futures::executor::block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();

		let mut subs =
			SubscriptionsInner::new(10, Duration::from_secs(10), MAX_OPERATIONS_PER_SUB, backend);
		let id_1 = "abc".to_string();
		let id_2 = "abcd".to_string();

		// Pin all blocks for the first subscription.
		let _stop = subs.insert_subscription(id_1.clone(), true).unwrap();
		assert_eq!(subs.pin_block(&id_1, hash_1).unwrap(), true);
		assert_eq!(subs.pin_block(&id_1, hash_2).unwrap(), true);
		assert_eq!(subs.pin_block(&id_1, hash_3).unwrap(), true);

		// Pin only block 2 for the second subscription.
		let _stop = subs.insert_subscription(id_2.clone(), true).unwrap();
		assert_eq!(subs.pin_block(&id_2, hash_2).unwrap(), true);

		// Check reference count.
		assert_eq!(*subs.global_blocks.get(&hash_1).unwrap(), 1);
		assert_eq!(*subs.global_blocks.get(&hash_2).unwrap(), 2);
		assert_eq!(*subs.global_blocks.get(&hash_3).unwrap(), 1);

		subs.remove_subscription(&id_1);

		assert!(subs.global_blocks.get(&hash_1).is_none());
		assert_eq!(*subs.global_blocks.get(&hash_2).unwrap(), 1);
		assert!(subs.global_blocks.get(&hash_3).is_none());

		subs.remove_subscription(&id_2);

		assert!(subs.global_blocks.get(&hash_2).is_none());
		assert_eq!(subs.global_blocks.len(), 0);
	}

	#[test]
	fn subscription_check_limits() {
		let (backend, mut client) = init_backend();
		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash_1 = block.header.hash();
		futures::executor::block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();
		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash_2 = block.header.hash();
		futures::executor::block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();
		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash_3 = block.header.hash();
		futures::executor::block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();

		// Maximum number of pinned blocks is 2.
		let mut subs =
			SubscriptionsInner::new(2, Duration::from_secs(10), MAX_OPERATIONS_PER_SUB, backend);
		let id_1 = "abc".to_string();
		let id_2 = "abcd".to_string();

		// Both subscriptions can pin the maximum limit.
		let _stop = subs.insert_subscription(id_1.clone(), true).unwrap();
		assert_eq!(subs.pin_block(&id_1, hash_1).unwrap(), true);
		assert_eq!(subs.pin_block(&id_1, hash_2).unwrap(), true);

		let _stop = subs.insert_subscription(id_2.clone(), true).unwrap();
		assert_eq!(subs.pin_block(&id_2, hash_1).unwrap(), true);
		assert_eq!(subs.pin_block(&id_2, hash_2).unwrap(), true);

		// Check reference count.
		assert_eq!(*subs.global_blocks.get(&hash_1).unwrap(), 2);
		assert_eq!(*subs.global_blocks.get(&hash_2).unwrap(), 2);

		// Block 3 pinning will exceed the limit and both subscriptions
		// are terminated because no subscription with older blocks than 10
		// seconds are present.
		let err = subs.pin_block(&id_1, hash_3).unwrap_err();
		assert_eq!(err, SubscriptionManagementError::ExceededLimits);

		// Ensure both subscriptions are removed.
		let err = subs.lock_block(&id_1, hash_1, 1).unwrap_err();
		assert_eq!(err, SubscriptionManagementError::SubscriptionAbsent);

		let err = subs.lock_block(&id_2, hash_1, 1).unwrap_err();
		assert_eq!(err, SubscriptionManagementError::SubscriptionAbsent);

		assert!(subs.global_blocks.get(&hash_1).is_none());
		assert!(subs.global_blocks.get(&hash_2).is_none());
		assert!(subs.global_blocks.get(&hash_3).is_none());
		assert_eq!(subs.global_blocks.len(), 0);
	}

	#[test]
	fn subscription_check_limits_with_duration() {
		let (backend, mut client) = init_backend();
		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash_1 = block.header.hash();
		futures::executor::block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();
		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash_2 = block.header.hash();
		futures::executor::block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();
		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash_3 = block.header.hash();
		futures::executor::block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();

		// Maximum number of pinned blocks is 2 and maximum pin duration is 5 second.
		let mut subs =
			SubscriptionsInner::new(2, Duration::from_secs(5), MAX_OPERATIONS_PER_SUB, backend);
		let id_1 = "abc".to_string();
		let id_2 = "abcd".to_string();

		let _stop = subs.insert_subscription(id_1.clone(), true).unwrap();
		assert_eq!(subs.pin_block(&id_1, hash_1).unwrap(), true);
		assert_eq!(subs.pin_block(&id_1, hash_2).unwrap(), true);

		// Maximum pin duration is 5 second, sleep 5 seconds to ensure we clean up
		// the first subscription.
		std::thread::sleep(std::time::Duration::from_secs(5));

		let _stop = subs.insert_subscription(id_2.clone(), true).unwrap();
		assert_eq!(subs.pin_block(&id_2, hash_1).unwrap(), true);

		// Check reference count.
		assert_eq!(*subs.global_blocks.get(&hash_1).unwrap(), 2);
		assert_eq!(*subs.global_blocks.get(&hash_2).unwrap(), 1);

		// Second subscription has only 1 block pinned. Only the first subscription is terminated.
		let err = subs.pin_block(&id_1, hash_3).unwrap_err();
		assert_eq!(err, SubscriptionManagementError::ExceededLimits);

		// Ensure both subscriptions are removed.
		let err = subs.lock_block(&id_1, hash_1, 1).unwrap_err();
		assert_eq!(err, SubscriptionManagementError::SubscriptionAbsent);

		let _block_guard = subs.lock_block(&id_2, hash_1, 1).unwrap();

		assert_eq!(*subs.global_blocks.get(&hash_1).unwrap(), 1);
		assert!(subs.global_blocks.get(&hash_2).is_none());
		assert!(subs.global_blocks.get(&hash_3).is_none());
		assert_eq!(subs.global_blocks.len(), 1);

		// Force second subscription to get terminated.
		assert_eq!(subs.pin_block(&id_2, hash_2).unwrap(), true);
		let err = subs.pin_block(&id_2, hash_3).unwrap_err();
		assert_eq!(err, SubscriptionManagementError::ExceededLimits);

		assert!(subs.global_blocks.get(&hash_1).is_none());
		assert!(subs.global_blocks.get(&hash_2).is_none());
		assert!(subs.global_blocks.get(&hash_3).is_none());
		assert_eq!(subs.global_blocks.len(), 0);
	}

	#[test]
	fn subscription_check_stop_event() {
		let builder = TestClientBuilder::new();
		let backend = builder.backend();
		let mut subs =
			SubscriptionsInner::new(10, Duration::from_secs(10), MAX_OPERATIONS_PER_SUB, backend);

		let id = "abc".to_string();

		let mut sub_data = subs.insert_subscription(id.clone(), true).unwrap();

		// Check the stop signal was not received.
		let res = sub_data.rx_stop.try_recv().unwrap();
		assert!(res.is_none());

		let sub = subs.subs.get_mut(&id).unwrap();
		sub.stop();

		// Check the signal was received.
		let res = sub_data.rx_stop.try_recv().unwrap();
		assert!(res.is_some());
	}

	#[test]
	fn ongoing_operations() {
		// The object can hold at most 2 operations.
		let ops = LimitOperations::new(2);

		// One operation is reserved.
		let permit_one = ops.reserve_at_most(1).unwrap();
		assert_eq!(permit_one.num_ops, 1);

		// Request 2 operations, however there is capacity only for one.
		let permit_two = ops.reserve_at_most(2).unwrap();
		// Number of reserved permits is smaller than provided.
		assert_eq!(permit_two.num_ops, 1);

		// Try to reserve operations when there's no space.
		let permit = ops.reserve_at_most(1);
		assert!(permit.is_none());

		// Release capacity.
		drop(permit_two);

		// Can reserve again
		let permit_three = ops.reserve_at_most(1).unwrap();
		assert_eq!(permit_three.num_ops, 1);
	}
}
