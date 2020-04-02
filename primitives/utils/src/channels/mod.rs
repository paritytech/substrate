// PURELY INTERNAL.
// REMOVE ONCE https://github.com/rust-lang/futures-rs/pull/2093 is resolved

use futures_core::stream::{FusedStream, Stream};
use futures_core::task::{Context, Poll, Waker};
use futures_core::task::__internal::AtomicWaker;
use std::fmt;
use std::pin::Pin;
use std::sync::{Arc, Mutex};
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering::SeqCst;

use crate::channels::queue::Queue;

mod queue;
#[cfg(feature = "sink")]
mod sink_impl;

/// Defines how the channel reacts when the user attempts
/// to send another message on a full queue
#[derive(Debug, PartialEq)]
pub enum OnFullStrategy {
    /// Apply backpressure, park thread
    /// Default
    Backpressure,
    /// Act as a RingBuffer: drop the first/oldest item
    /// in the queue to make space and added the new item
    Ring,
    /// Ignore the newly added item without adding
    Ignore,
    /// Error with `FullCapacity`Receiver
    Error
}

impl Default for OnFullStrategy {
    fn default() -> Self {
        OnFullStrategy::Backpressure
    }
}

#[derive(Debug)]
struct SenderInner<T> {
    // Channel state shared between the sender and receiver.
    inner: Arc<Inner<T>>,

    // Handle to the task that is blocked on this sender. This handle is sent
    // to the receiver half in order to be notified when the sender becomes
    // unblocked.
    sender_task: Arc<Mutex<SenderTask>>,

    // `true` if the sender might be blocked. This is an optimization to avoid
    // having to lock the mutex most of the time.
    maybe_parked: bool,
}

/// The transmission end of a bounded mpsc channel.
///
/// This value is created by the [`channel`](channel) function.
#[derive(Debug)]
pub struct Sender<T>(Option<SenderInner<T>>);

/// The transmission end of an unbounded mpsc channel.
///
/// This value is created by the [`unbounded`](unbounded) function.
pub type UnboundedSender<T> = Sender<T>;

trait AssertKinds: Send + Sync + Clone {}
impl AssertKinds for Sender<u32> {}

/// The receiving end of a bounded mpsc channel.
///
/// This value is created by the [`channel`](channel) function.
#[derive(Debug)]
pub struct Receiver<T> {
    inner: Option<Arc<Inner<T>>>,
}

/// The receiving end of an unbounded mpsc channel.
///
/// This value is created by the [`unbounded`](unbounded) function.
pub type UnboundedReceiver<T> = Receiver<T>;

/// The error type for [`Sender`s](Sender) used as `Sink`s.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SendError {
    kind: SendErrorKind,
}

/// The error type returned from [`try_send`](Sender::try_send).
#[derive(Clone, PartialEq, Eq)]
pub struct TrySendError<T> {
    err: SendError,
    val: T,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum SendErrorKind {
    Full,
    Ignored,
    Disconnected,
}

/// The error type returned from [`try_next`](Receiver::try_next).
pub struct TryRecvError {
    _priv: (),
}

impl fmt::Display for SendError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_full() {
            write!(f, "send failed because channel is full")
        } else {
            write!(f, "send failed because receiver is gone")
        }
    }
}

impl std::error::Error for SendError {}

impl SendError {
    /// Returns `true` if this error is a result of the channel being full.
    pub fn is_full(&self) -> bool {
        match self.kind {
            SendErrorKind::Full => true,
            _ => false,
        }
    }

    /// Returns `true` if this error is a result of the receiver being dropped.
    pub fn is_disconnected(&self) -> bool {
        match self.kind {
            SendErrorKind::Disconnected => true,
            _ => false,
        }
    }
}

impl<T> fmt::Debug for TrySendError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TrySendError")
            .field("kind", &self.err.kind)
            .finish()
    }
}

impl<T> fmt::Display for TrySendError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_full() {
            write!(f, "send failed because channel is full")
        } else {
            write!(f, "send failed because receiver is gone")
        }
    }
}

impl<T: core::any::Any> std::error::Error for TrySendError<T> {}

impl<T> TrySendError<T> {
    /// Returns `true` if this error is a result of the channel being full.
    pub fn is_full(&self) -> bool {
        self.err.is_full()
    }

    /// Returns `true` if this error is a result of the receiver being dropped.
    pub fn is_disconnected(&self) -> bool {
        self.err.is_disconnected()
    }

    /// Returns the message that was attempted to be sent but failed.
    pub fn into_inner(self) -> T {
        self.val
    }

    /// Drops the message and converts into a `SendError`.
    pub fn into_send_error(self) -> SendError {
        self.err
    }
}

impl fmt::Debug for TryRecvError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("TryRecvError")
            .finish()
    }
}

impl fmt::Display for TryRecvError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "receiver channel is empty")
    }
}

impl std::error::Error for TryRecvError {}

type SendTaskRef = Arc<Mutex<SenderTask>>;

#[derive(Debug)]
struct Inner<T> {
    // Max buffer size of the channel
    buffer: usize,

    // How to react if the channel is full
    full_strategy: OnFullStrategy,

    // Internal channel state. Consists of the number of messages stored in the
    // channel as well as a flag signalling that the channel is closed.
    state: AtomicUsize,

    // Atomic, FIFO queue used to send messages to the receiver
    message_queue: Queue<T>,

    // Atomic, FIFO queue used to send parked task handles to the receiver.
    parked_queue: Queue<SendTaskRef>,

    // Number of senders in existence
    num_senders: AtomicUsize,

    // Handle to the receiver's task.
    recv_task: AtomicWaker,
}


impl<T> Inner<T> {

    fn dec_num_messages(&self) {
        // OPEN_MASK is highest bit, so it's unaffected by subtraction
        // unless there's underflow, and we know there's no underflow
        // because number of messages at this point is always > 0.
        self.state.fetch_sub(1, SeqCst);
    }

    // Increment the number of queued messages, return how many are
    // left before the limit is reached.
    fn inc_num_messages(&self) -> Result<usize, SendErrorKind> {
        let mut curr = self.state.load(SeqCst);

        loop {
            let mut state = decode_state(curr);

            // The receiver end closed the channel.
            if !state.is_open {
                return Err(SendErrorKind::Disconnected);
            }

            state.num_messages += 1;

            let remaining = match self.buffer.checked_sub(state.num_messages) {
                // we are full, but maybe have a way to handle it.
                None => match self.full_strategy {
                    OnFullStrategy::Ring => {
                        // dropping the first, trying again
                        if let Poll::Ready(Some(_)) = self.next_message() {
                            // and try again
                            curr = self.state.load(SeqCst);
                            continue
                        } else {
                            return Err(SendErrorKind::Disconnected)
                        }
                    }
                    OnFullStrategy::Ignore => {
                        // return without updating the value
                        return Err(SendErrorKind::Ignored)
                    }
                    // Update the value, but escalate the error
                    _ => Err(SendErrorKind::Full)
                },
                Some(x) => Ok(x)
            };

            let next = encode_state(&state);
            match self.state.compare_exchange(curr, next, SeqCst, SeqCst) {
                Ok(_) => return remaining, 
                Err(actual) => curr = actual,
            }
        }
    }

    fn queue_msg_and_notify(&self, msg: T) {

        // Push the message onto the message queue
        self.message_queue.push(msg);
        // Signal to the receiver that a message has been enqueued. If the
        // receiver is parked, this will unpark the task.p
        self.recv_task.wake();
        
    }

    fn next_message(&self) -> Poll<Option<T>> {
        // Pop off a message
        match unsafe { self.message_queue.pop_spin() } {
            Some(msg) => {

                // Decrement number of messages
                self.dec_num_messages();

                // unpark one sender
                self.unpark_one();

                Poll::Ready(Some(msg))
            }
            None => {
                let state = decode_state(self.state.load(SeqCst));
                if state.is_open || state.num_messages != 0 {
                    // If queue is open, we need to return Pending
                    // to be woken up when new messages arrive.
                    // If queue is closed but num_messages is non-zero,
                    // it means that senders updated the state,
                    // but didn't put message to queue yet,
                    // so we need to park until sender unparks the task
                    // after queueing the message.
                    Poll::Pending
                } else {
                    // If closed flag is set AND there are no pending messages
                    // it means end of stream
                    Poll::Ready(None)
                }
            }
        }
    }

    // Unpark a single task handle if there is one pending in the parked queue
    fn unpark_one(&self) {
        if let Some(task) = unsafe { self.parked_queue.pop_spin() } {
            task.lock().unwrap().notify();
        }
    }

}

// Struct representation of `Inner::state`.
#[derive(Debug, Clone, Copy)]
struct State {
    // `true` when the channel is open
    is_open: bool,

    // Number of messages in the channel
    num_messages: usize,
}

// The `is_open` flag is stored in the left-most bit of `Inner::state`
const OPEN_MASK: usize = usize::max_value() - (usize::max_value() >> 1);

// When a new channel is created, it is created in the open state with no
// pending messages.
const INIT_STATE: usize = OPEN_MASK;

// The maximum number of messages that a channel can track is `usize::max_value() >> 1`
const MAX_CAPACITY: usize = !(OPEN_MASK);

// The maximum requested buffer size must be less than the maximum capacity of
// a channel. This is because each sender gets a guaranteed slot.
const MAX_BUFFER: usize = MAX_CAPACITY >> 1;

// Sent to the consumer to wake up blocked producers
#[derive(Debug)]
struct SenderTask {
    task: Option<Waker>,
    is_parked: bool,
}

impl SenderTask {
    fn new() -> Self {
        SenderTask {
            task: None,
            is_parked: false,
        }
    }

    fn notify(&mut self) {
        self.is_parked = false;

        if let Some(task) = self.task.take() {
            task.wake();
        }
    }
}

/// Creates a bounded mpsc channel for communicating between asynchronous tasks.
///
/// Being bounded, this channel provides backpressure to ensure that the sender
/// outpaces the receiver by only a limited amount.
/// See [`channel_with_strategy`](channel_with_strategy) for more.
pub fn channel<T>(buffer: usize) -> (Sender<T>, Receiver<T>) {
    channel_with_strategy(buffer, OnFullStrategy::Backpressure)
}

/// Creates an mpsc channel for communicating between asynchronous tasks with the
/// given full management strategy.
/// 
/// The channel's capacity is equal to `buffer + num-senders`. In other words,
/// each sender gets a guaranteed slot in the channel capacity, and on top of
/// that there are `buffer` "first come, first serve" slots available to all
/// senders.
///
/// The [`Receiver`](Receiver) returned implements the
/// [`Stream`](futures_core::stream::Stream) trait, while [`Sender`](Sender) implements
/// `Sink`.
pub fn channel_with_strategy<T>(buffer: usize, full_strategy: OnFullStrategy) -> (Sender<T>, Receiver<T>) {
    // Check that the requested buffer size does not exceed the maximum buffer
    // size permitted by the system.
    assert!(buffer < MAX_BUFFER, "requested buffer size too large");

    let inner = Arc::new(Inner {
        buffer,
        full_strategy,
        state: AtomicUsize::new(INIT_STATE),
        message_queue: Queue::new(),
        parked_queue: Queue::new(),
        num_senders: AtomicUsize::new(1),
        recv_task: AtomicWaker::new(),
    });

    let tx = SenderInner {
        inner: inner.clone(),
        sender_task: Arc::new(Mutex::new(SenderTask::new())),
        maybe_parked: false,
    };

    let rx = Receiver {
        inner: Some(inner),
    };

    (Sender(Some(tx)), rx)
}

/// Creates an unbounded mpsc channel for communicating between asynchronous
/// tasks.
///
/// A `send` on this channel will always succeed as long as the receive half has
/// not been closed. If the receiver falls behind, messages will be arbitrarily
/// buffered.
///
/// **Note** that the amount of available system memory is an implicit bound to
/// the channel. Using an `unbounded` channel has the ability of causing the
/// process to run out of memory. In this case, the process will be aborted.
pub fn unbounded<T>() -> (UnboundedSender<T>, UnboundedReceiver<T>) {
    channel_with_strategy(MAX_BUFFER - 1, OnFullStrategy::Error)
}

impl<T> SenderInner<T> {
    /// Attempts to send a message on this `Sender`, returning the message
    /// if there was an error.
    fn send_mut(&mut self, msg: T) -> Result<(), TrySendError<T>> {
        // If the sender is currently blocked, reject the message
        if !self.poll_unparked(None).is_ready() {
            return Err(TrySendError {
                err: SendError {
                    kind: SendErrorKind::Full,
                },
                val: msg,
            });
        }
        
        let result = self.send(msg);
        
        match result {
            Err(TrySendError {
                err: SendError {
                    kind: SendErrorKind::Full,
                },
                val: msg,
            }) if self.inner.full_strategy == OnFullStrategy::Backpressure => {
                self.park();
                self.inner.queue_msg_and_notify(msg);
                Ok(())
            }
            _ => result
        }
    }

    fn park(&mut self) {
        {
            let mut sender = self.sender_task.lock().unwrap();
            sender.task = None;
            sender.is_parked = true;
        }

        self.inner.parked_queue.push(self.sender_task.clone());

        // we do not want to park, if
        // Check to make sure we weren't closed after we sent our task on the
        // queue
        let state = decode_state(self.inner.state.load(SeqCst));
        self.maybe_parked = state.is_open;
        // and we continue
    }

    fn send(&self, msg: T) -> Result<(), TrySendError<T>> {
        if let Err(e) = self.inner.inc_num_messages() {
            if e == SendErrorKind::Ignored {
                // we just don't mind and drop the value
                return Ok(())
            } else {
                return Err(TrySendError {
                    err: SendError {
                        kind: e,
                    },
                    val: msg,
                });
            }
        }

        self.inner.queue_msg_and_notify(msg);
        Ok(())
    }

    /// Polls the channel to determine if there is guaranteed capacity to send
    /// at least one item without waiting.
    ///
    /// # Return value
    ///
    /// This method returns:
    ///
    /// - `Poll::Ready(Ok(_))` if there is sufficient capacity;
    /// - `Poll::Pending` if the channel may not have
    ///   capacity, in which case the current task is queued to be notified once
    ///   capacity is available;
    /// - `Poll::Ready(Err(SendError))` if the receiver has been dropped.
    fn poll_ready(
        &mut self,
        cx: &mut Context<'_>,
    ) -> Poll<Result<(), SendError>> {
        let state = decode_state(self.inner.state.load(SeqCst));
        if !state.is_open {
            return Poll::Ready(Err(SendError {
                kind: SendErrorKind::Disconnected,
            }));
        }

        self.poll_unparked(Some(cx)).map(Ok)
    }

    /// Returns whether the senders send to the same receiver.
    fn same_receiver(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.inner, &other.inner)
    }

    /// Returns pointer to the Arc containing sender
    ///
    /// The returned pointer is not referenced and should be only used for hashing!
    fn ptr(&self) -> *const Inner<T> {
        &*self.inner
    }

    /// Returns whether this channel is closed without needing a context.
    fn is_closed(&self) -> bool {
        !decode_state(self.inner.state.load(SeqCst)).is_open
    }

    /// Closes this channel from the sender side, preventing any new messages.
    fn close_channel(&self) {
        // There's no need to park this sender, its dropping,
        // and we don't want to check for capacity, so skip
        // that stuff from `do_send`.

        self.inner.set_closed();
        self.inner.recv_task.wake();
    }

    fn poll_unparked(&mut self, cx: Option<&mut Context<'_>>) -> Poll<()> {
        // First check the `maybe_parked` variable. This avoids acquiring the
        // lock in most cases
        if self.maybe_parked {
            // Get a lock on the task handle
            let mut task = self.sender_task.lock().unwrap();

            if !task.is_parked {
                self.maybe_parked = false;
                return Poll::Ready(())
            }

            // At this point, an unpark request is pending, so there will be an
            // unpark sometime in the future. We just need to make sure that
            // the correct task will be notified.
            //
            // Update the task in case the `Sender` has been moved to another
            // task
            task.task = cx.map(|cx| cx.waker().clone());

            Poll::Pending
        } else {
            Poll::Ready(())
        }
    }
}

impl<T> Sender<T> {
    /// Attempts to send a message on this `Sender`, returning the message
    /// if there was an error.
    pub fn try_send(&mut self, msg: T) -> Result<(), TrySendError<T>> {
        if let Some(inner) = &mut self.0 {
            inner.send_mut(msg)
        } else {
            Err(TrySendError {
                err: SendError {
                    kind: SendErrorKind::Disconnected,
                },
                val: msg,
            })
        }
    }

    /// Send a message on the channel.
    ///
    /// This function should only be called after
    /// [`poll_ready`](Sender::poll_ready) has reported that the channel is
    /// ready to receive a message.
    pub fn start_send(&mut self, msg: T) -> Result<(), SendError> {
        self.try_send(msg)
            .map_err(|e| e.err)
    }

    ///
    pub fn unbounded_send(&self, msg: T) -> Result<(), TrySendError<T>> {
        if let Some(inner) = &self.0 {
            inner.send(msg)
        } else {
            Err(TrySendError {
                err: SendError {
                    kind: SendErrorKind::Disconnected,
                },
                val: msg,
            })
        }
    }

    /// Polls the channel to determine if there is guaranteed capacity to send
    /// at least one item without waiting.
    ///
    /// # Return value
    ///
    /// This method returns:
    ///
    /// - `Poll::Ready(Ok(_))` if there is sufficient capacity;
    /// - `Poll::Pending` if the channel may not have
    ///   capacity, in which case the current task is queued to be notified once
    ///   capacity is available;
    /// - `Poll::Ready(Err(SendError))` if the receiver has been dropped.
    pub fn poll_ready(
        &mut self,
        cx: &mut Context<'_>,
    ) -> Poll<Result<(), SendError>> {
        let inner = self.0.as_mut().ok_or(SendError {
            kind: SendErrorKind::Disconnected,
        })?;
        inner.poll_ready(cx)
    }

    /// Returns whether this channel is closed without needing a context.
    pub fn is_closed(&self) -> bool {
        self.0.as_ref().map(SenderInner::is_closed).unwrap_or(true)
    }

    /// Closes this channel from the sender side, preventing any new messages.
    pub fn close_channel(&self) {
        if let Some(inner) = &self.0 {
            inner.close_channel();
        }
    }

    /// Disconnects this sender from the channel, closing it if there are no more senders left.
    pub fn disconnect(&mut self) {
        self.0 = None;
    }

    /// Returns whether the senders send to the same receiver.
    pub fn same_receiver(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (Some(inner), Some(other)) => inner.same_receiver(other),
            _ => false,
        }
    }

    /// Hashes the receiver into the provided hasher
    pub fn hash_receiver<H>(&self, hasher: &mut H) where H: std::hash::Hasher {
        use std::hash::Hash;

        let ptr = self.0.as_ref().map(|inner| inner.ptr());
        ptr.hash(hasher);
    }
}

impl<T> Clone for Sender<T> {
    fn clone(&self) -> Sender<T> {
        Sender(self.0.clone())
    }
}

impl<T> Clone for SenderInner<T> {
    fn clone(&self) -> SenderInner<T> {
        // Since this atomic op isn't actually guarding any memory and we don't
        // care about any orderings besides the ordering on the single atomic
        // variable, a relaxed ordering is acceptable.
        let mut curr = self.inner.num_senders.load(SeqCst);

        loop {
            // If the maximum number of senders has been reached, then fail
            if curr == self.inner.max_senders() {
                panic!("cannot clone `Sender` -- too many outstanding senders");
            }

            debug_assert!(curr < self.inner.max_senders());

            let next = curr + 1;
            let actual = self.inner.num_senders.compare_and_swap(curr, next, SeqCst);

            // The ABA problem doesn't matter here. We only care that the
            // number of senders never exceeds the maximum.
            if actual == curr {
                return SenderInner {
                    inner: self.inner.clone(),
                    sender_task: Arc::new(Mutex::new(SenderTask::new())),
                    maybe_parked: false,
                };
            }

            curr = actual;
        }
    }
}

impl<T> Drop for SenderInner<T> {
    fn drop(&mut self) {
        // Ordering between variables don't matter here
        let prev = self.inner.num_senders.fetch_sub(1, SeqCst);

        if prev == 1 {
            self.close_channel();
        }
    }
}

/*
 *
 * ===== impl Receiver =====
 *
 */

impl<T> Receiver<T> {
    /// Closes the receiving half of a channel, without dropping it.
    ///
    /// This prevents any further messages from being sent on the channel while
    /// still enabling the receiver to drain messages that are buffered.
    pub fn close(&mut self) {
        if let Some(inner) = &mut self.inner {
            inner.set_closed();

            // Wake up any threads waiting as they'll see that we've closed the
            // channel and will continue on their merry way.
            while let Some(task) = unsafe { inner.parked_queue.pop_spin() } {
                task.lock().unwrap().notify();
            }
        }
    }

    /// Tries to receive the next message without notifying a context if empty.
    ///
    /// It is not recommended to call this function from inside of a future,
    /// only when you've otherwise arranged to be notified when the channel is
    /// no longer empty.
    ///
    /// This function will panic if called after `try_next` or `poll_next` has
    /// returned `None`.
    pub fn try_next(&mut self) -> Result<Option<T>, TryRecvError> {
        match self.next_message() {
            Poll::Ready(msg) => {
                Ok(msg)
            },
            Poll::Pending => Err(TryRecvError { _priv: () }),
        }
    }

    fn next_message(&mut self) -> Poll<Option<T>> {
        let next = self.inner
            .as_mut()
            .expect("Receiver::next_message called after `None`")
            .next_message();

        match next {
            Poll::Ready(None) => {
                // closed
                self.inner = None;
            }
            _ => {}
        }

        next
    }
}

// The receiver does not ever take a Pin to the inner T
impl<T> Unpin for Receiver<T> {}

impl<T> FusedStream for Receiver<T> {
    fn is_terminated(&self) -> bool {
        self.inner.is_none()
    }
}

impl<T> Stream for Receiver<T> {
    type Item = T;

    fn poll_next(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Option<T>> {
            // Try to read a message off of the message queue.
        match self.next_message() {
            Poll::Ready(msg) => {
                if msg.is_none() {
                    self.inner = None;
                }
                Poll::Ready(msg)
            },
            Poll::Pending => {
                // There are no messages to read, in this case, park.
                self.inner.as_ref().unwrap().recv_task.register(cx.waker());
                // Check queue again after parking to prevent race condition:
                // a message could be added to the queue after previous `next_message`
                // before `register` call.
                self.next_message()
            }
        }
    }
}

impl<T> Drop for Receiver<T> {
    fn drop(&mut self) {
        // Drain the channel of all pending messages
        self.close();
        if self.inner.is_some() {
            while let Poll::Ready(Some(..)) = self.next_message() {
                // ...
            }
        }
    }
}

/*
 *
 * ===== impl Inner =====
 *
 */

impl<T> Inner<T> {
    // The return value is such that the total number of messages that can be
    // enqueued into the channel will never exceed MAX_CAPACITY
    fn max_senders(&self) -> usize {
        MAX_CAPACITY - self.buffer
    }

    // Clear `open` flag in the state, keep `num_messages` intact.
    fn set_closed(&self) {
        let curr = self.state.load(SeqCst);
        if !decode_state(curr).is_open {
            return;
        }

        self.state.fetch_and(!OPEN_MASK, SeqCst);
    }
}

unsafe impl<T: Send> Send for Inner<T> {}
unsafe impl<T: Send> Sync for Inner<T> {}
/*
 *
 * ===== Helpers =====
 *
 */

fn decode_state(num: usize) -> State {
    State {
        is_open: num & OPEN_MASK == OPEN_MASK,
        num_messages: num & MAX_CAPACITY,
    }
}

fn encode_state(state: &State) -> usize {
    let mut num = state.num_messages;

    if state.is_open {
        num |= OPEN_MASK;
    }

    num
}
