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

use sp_std::{rc::Rc, collections::btree_map::BTreeMap, vec::Vec};
use sp_std::cell::RefCell;

use core::pin::Pin;
use core::future::Future;
use core::{task::{self, Context, Poll, Waker}};

use spin::Mutex;

pub(crate) type MessageId = u64;

// TODO: Decode actual events
pub(crate) struct Message(Vec<u8>);

fn epoll_peek(interest_list: &[MessageId]) -> MessageId {
    unimplemented!()
}

fn epoll_wait(interest_list: &[MessageId]) -> MessageId {
    unimplemented!()
}

fn decode(id: MessageId) -> Message {
    unimplemented!()
}

pub(crate) fn next_notification(interest_list: &[MessageId], block: bool) -> Option<(Message, MessageId, usize)> {
    let id = if !block { epoll_peek(interest_list) } else { epoll_wait(interest_list) };

    // TODO: Handle FFI boundary and output bytes
    Some((
        decode(id),
        // TODO: Fetch message_id from interest_list
        0,
        // TODO: Fetch index from interest_list
        0,
    ))
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

// TODO: Executor + reactor for wasm-side futures, waits on host-executed
// futures like HTTP requests etc.
pub fn block_on<T>(future: impl Future<Output = T>) -> T {
    pin_mut!(future);

    // We don't have `Arc` to use convenient `ArcWake` and we're always running
    // on a single thread in WASM so ¯\_(ツ)_/¯
    fn trigger_wakeup(data: *const ()) {
        let data: *const RefCell<bool> = data as _;
        unsafe { *(*data).borrow_mut() = true; }
    };
    fn drop_shared_wakeup(data: *const ()) {
        unsafe { Rc::from_raw(data as *const RefCell<bool>); }
    }
    fn create_waker(data: *const()) -> core::task::RawWaker {
        let data = unsafe { Rc::from_raw(data as *const RefCell<bool>) };
        let cloned = Rc::clone(&data);
        core::task::RawWaker::new(Rc::into_raw(cloned) as _, &core::task::RawWakerVTable::new(
            create_waker,
            |data| { trigger_wakeup(data); drop_shared_wakeup(data) },
            trigger_wakeup,
            drop_shared_wakeup,
        ))
    }

    let woken_up = Rc::new(RefCell::new(false));
    let waker = {
        let raw = create_waker(Rc::into_raw(Rc::clone(&woken_up)) as _);
        unsafe { task::Waker::from_raw(raw) }
    };

    let mut context = Context::from_waker(&waker);

    loop {
        // We poll the future continuously until it is either Ready, or the waker stops being
        // invoked during the polling.
        loop {
            if let Poll::Ready(val) = Future::poll(future.as_mut(), &mut context) {
                return val;
            }

            // If the waker has been used during the polling of this future,
            // then we have to poll again.
            let was_woken = *woken_up.borrow();
            *woken_up.borrow_mut() = false;

            if was_woken {
                continue;
            } else {
                break;
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
    message_ids: Vec<u64>,

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
