#![allow(dead_code, unused_variables)]

// Based on https://github.com/tomaka/redshirt/blob/802e4ab44078e15b47dc72afc6b7e45bab1b72df/interfaces/syscalls/src/block_on.rs#L88.

/// Pins a value on the stack.
// A copy of `futures::pin_mut!` without having to pull `futures` in the no_std
// context.
macro_rules! pin_mut {
    ($($x:ident),* $(,)?) => { $(
        // Move the value to ensure that it is owned
        let mut $x = $x;
        // Shadow the original binding so that it can't be directly accessed
        // ever again.
        #[allow(unused_mut)]
        let mut $x = unsafe {
            core::pin::Pin::new_unchecked(&mut $x)
        };
    )* }
}

use sp_core::offchain::{PollableId, PollableKind};
use sp_std::{rc::Rc, collections::btree_map::BTreeMap, vec::Vec};
use sp_std::cell::RefCell;

use core::future::Future;
use core::mem::{self, ManuallyDrop};
use core::pin::Pin;
use core::{task::{self, Context, Poll, Waker, RawWaker, RawWakerVTable}};

use spin::Mutex;

pub(crate) type MessageId = PollableId;

// TODO: Decode actual events
pub(crate) struct Message(Vec<u8>);

fn epoll_peek(interest_list: &[MessageId]) -> Option<MessageId> {
    let deadline = super::offchain::timestamp();
    super::offchain::pollable_wait(interest_list, Some(deadline))
}

fn epoll_wait(interest_list: &[MessageId]) -> MessageId {
    super::offchain::pollable_wait(interest_list, None)
        .expect(
            "pollable_wait with None deadline should block indefinitely \
            until we get a response; qed"
        )
}

fn decode(id: MessageId) -> Message {
    // TODO: Handle FFI boundary and output bytes
    match id.kind() {
        PollableKind::Http | _ => unimplemented!(),
    }
}

pub(crate) fn next_notification(interest_list: &[MessageId], block: bool) -> Option<(Message, MessageId, usize)> {
    let id = if !block {
        epoll_peek(interest_list)
    } else {
        Some(epoll_wait(interest_list))
    }?;

    let pos = interest_list.iter().position(|&x| x == id)
        .expect("pollable API should only return an ID from the interest list; qed");

    Some((decode(id), id, pos))
}

/// Registers a message ID and a waker. The `block_on` function will
/// then ask the kernel for a message corresponding to this ID. If one is received, the `Waker`
/// is called.
///
/// For non-interface messages, there can only ever be one registered `Waker`. Registering a
/// `Waker` a second time overrides the one previously registered.
pub(crate) fn register_message_waker(message_id: MessageId, waker: Waker) {
    let mut state = (&*STATE).lock();

    if let Some(pos) = state
        .message_ids
        .iter()
        .position(|msg| *msg == From::from(message_id))
    {
        state.wakers[pos] = waker;
        return;
    }

    state.message_ids.push(From::from(message_id));
    state.wakers.push(waker);
}

// Copied `alloc::task::Wake` without having to opt-in via `#![feature(wake_trait)]`
// https://github.com/rust-lang/rust/pull/68700
trait Wake {
    fn wake(self: Rc<Self>);
    fn wake_by_ref(self: &Rc<Self>) {
        self.clone().wake();
    }
}

// Work around being unable to impl Into<Waker> for Rc<T> due to coherence check
// and blanket impls
trait IntoWaker: Wake {
    fn into_waker(self: Rc<Self>) -> Waker;
}

impl<T> IntoWaker for T where T: Wake + Send + 'static {
    fn into_waker(self: Rc<Self>) -> Waker {
        // SAFETY: This is safe because raw_waker safely constructs
        // a RawWaker from Rc<W> where W: Wake.
        unsafe { task::Waker::from_raw(raw_waker(self)) }
    }
}

#[inline(always)]
fn raw_waker<W: Wake + Send + 'static>(waker: Rc<W>) -> RawWaker {
    // Increment the reference count of the arc to clone it.
    unsafe fn clone_waker<W: Wake + Send + 'static>(waker: *const ()) -> RawWaker {
        let waker: Rc<W> = Rc::from_raw(waker as *const W);
        mem::forget(Rc::clone(&waker));
        raw_waker(waker)
    }

    // Wake by value, moving the Arc into the Wake::wake function
    unsafe fn wake<W: Wake + Send + 'static>(waker: *const ()) {
        let waker: Rc<W> = Rc::from_raw(waker as *const W);
        <W as Wake>::wake(waker);
    }

    // Wake by reference, wrap the waker in ManuallyDrop to avoid dropping it
    unsafe fn wake_by_ref<W: Wake + Send + 'static>(waker: *const ()) {
        let waker: ManuallyDrop<Rc<W>> = ManuallyDrop::new(Rc::from_raw(waker as *const W));
        <W as Wake>::wake_by_ref(&waker);
    }

    // Decrement the reference count of the Arc on drop
    unsafe fn drop_waker<W: Wake + Send + 'static>(waker: *const ()) {
        mem::drop(Rc::from_raw(waker as *const W));
    }

    RawWaker::new(
        Rc::into_raw(waker) as *const (),
        &RawWakerVTable::new(clone_waker::<W>, wake::<W>, wake_by_ref::<W>, drop_waker::<W>),
    )
}

// TODO: Executor + reactor for wasm-side futures, waits on host-executed
// futures like HTTP requests etc.
pub fn block_on<T>(future: impl Future<Output = T>) -> T {
    pin_mut!(future);

    struct WokenUp(RefCell<bool>);
    impl Wake for WokenUp {
        fn wake(self: Rc<Self>) {
            *self.0.borrow_mut() = true;
        }
    }

    let woken_up = Rc::new(WokenUp(RefCell::new(false)));

    let waker = woken_up.clone().into_waker();
    let mut context = Context::from_waker(&waker);

    loop {
        // We poll the future continuously until it is either Ready, or the waker stops being
        // invoked during the polling.
        loop {
            match future.as_mut().poll(&mut context) {
                Poll::Ready(value) => return value,
                // If the waker has been used during the polling of this future,
                // then we have to poll again.
                Poll::Pending if mem::replace(&mut *woken_up.0.borrow_mut(), false) => {},
                // Otherwise, we need to wait for an external notification for
                // this future to make progress.
                Poll::Pending => break,
            }
        }

        let mut state = (&*STATE).lock();
        debug_assert_eq!(state.message_ids.len(), state.wakers.len());

        // `block` indicates whether we should block the thread or just peek.
        // Always `true` during the first iteration, and `false` in further iterations.
        let mut block = true;

        // We process in a loop all pending messages.
        while let Some((msg, message_id, index_in_list)) = next_notification(&mut state.message_ids, block) {
            block = false;

            let _was_in = state.message_ids.remove(index_in_list as usize);

            let waker = state.wakers.remove(index_in_list as usize);
            waker.wake();

            let _was_in = state.pending_messages.insert(message_id, msg);
            debug_assert!(_was_in.is_none());
        }

        debug_assert!(!block);
    }
}

lazy_static::lazy_static! {
    // TODO: we're using a Mutex, which is ok for as long as WASM doesn't have threads
    // if WASM ever gets threads and no pre-emptive multitasking, then we might spin forever
    static ref STATE: Mutex<BlockOnState> = {
        Mutex::new(BlockOnState {
            message_ids: Vec::new(),
            wakers: Vec::new(),
            pending_messages: BTreeMap::new(),
        })
    };
}

/// State of the global `block_on` mechanism.
///
/// This is instantiated only once.
struct BlockOnState {
    /// List of messages for which we are waiting for a response. A pointer to this list is passed
    /// to the kernel.
    message_ids: Vec<MessageId>,

    /// List whose length is identical to [`BlockOnState::messages_ids`]. For each element in
    /// [`BlockOnState::messages_ids`], contains a corresponding `Waker` that must be waken up
    /// when a response comes.
    wakers: Vec<Waker>,

    /// Queue of response messages waiting to be delivered.
    ///
    /// > **Note**: We have to maintain this queue as a global variable rather than a per-future
    /// >           channel, otherwise dropping a `Future` would silently drop messages that have
    /// >           already been received.
    pending_messages: BTreeMap<MessageId, Message>,
}

/// Future that drives `message_response` to completion.
#[must_use = "futures do nothing unless polled"]
pub(crate) struct MessageResponseFuture {
    msg_id: MessageId,
    finished: bool,
}

impl Future for MessageResponseFuture {
    type Output = Message;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
        assert!(!self.finished);
        if let Some(response) = peek_response(self.msg_id) {
            self.finished = true;
            Poll::Ready(response)
        } else {
            register_message_waker(self.msg_id, cx.waker().clone());
            Poll::Pending
        }
    }
}

/// If a response to this message ID has previously been obtained, extracts it for processing.
pub(crate) fn peek_response(msg_id: MessageId) -> Option<Message> {
    let mut state = (&*STATE).lock();
    state.pending_messages.remove(&msg_id)
}
