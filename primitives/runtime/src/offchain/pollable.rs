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
use sp_std::{rc::Rc, collections::btree_set::BTreeSet, vec::Vec};
use sp_std::cell::RefCell;

use core::future::Future;
use core::mem::{self, ManuallyDrop};
use core::pin::Pin;
use core::{task::{self, Context, Poll, Waker, RawWaker, RawWakerVTable}};

use spin::Mutex;
use pin_project::pin_project;

pub(crate) type MessageId = PollableId;

fn epoll_peek(interest_list: &[MessageId]) -> Option<MessageId> {
    let deadline = sp_io::offchain::timestamp();
    sp_io::offchain::pollable_wait(interest_list, Some(deadline))
}

fn epoll_wait(interest_list: &[MessageId]) -> MessageId {
    sp_io::offchain::pollable_wait(interest_list, None)
        .expect(
            "pollable_wait with None deadline should block indefinitely \
            until we get a response; qed"
        )
}

pub(crate) fn next_notification(interest_list: &[MessageId], block: bool) -> Option<(MessageId, usize)> {
    let id = if !block {
        epoll_peek(interest_list)
    } else {
        Some(epoll_wait(interest_list))
    }?;

    let pos = interest_list.iter().position(|&x| x == id)
        .expect("pollable API should only return an ID from the interest list; qed");

    Some((id, pos))
}

/// Registers a message ID and a waker. The `block_on` function will
/// then ask the kernel for a message corresponding to this ID. If one is received, the `Waker`
/// is called.
///
/// For non-interface messages, there can only ever be one registered `Waker`. Registering a
/// `Waker` a second time overrides the one previously registered.
pub(crate) fn register_message_waker(message_id: MessageId, waker: Waker) {
    let mut state = STATE.lock();

    if let Some(pos) = state
        .message_ids
        .iter()
        .position(|msg| *msg == message_id)
    {
        state.wakers[pos] = waker;
        return;
    }

    state.message_ids.push(message_id);
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
                Poll::Pending if mem::replace(&mut *woken_up.0.borrow_mut(), false) => continue,
                // Otherwise, we need to wait for an external notification for
                // this future to make progress.
                Poll::Pending => break,
            }
        }

        let mut state = STATE.lock();
        debug_assert_eq!(state.message_ids.len(), state.wakers.len());

        // `block` indicates whether we should block the thread or just peek.
        // Always `true` during the first iteration, and `false` in further iterations.
        let mut block = true;

        // We process in a loop all pending messages.
        while let Some((message_id, index_in_list)) = next_notification(&mut state.message_ids, block) {
            block = false;

            state.message_ids.remove(index_in_list);
            let waker = state.wakers.remove(index_in_list);
            waker.wake();

            let _new_msg_id = state.pending_messages.insert(message_id);
            debug_assert!(_new_msg_id);
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
            pending_messages: BTreeSet::new(),
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
    pending_messages: BTreeSet<MessageId>,
}

/// Future that's resolved whenever the `PollableId` is signalled as ready by
/// the Substrate host.
#[must_use = "futures do nothing unless polled"]
#[derive(Debug)]
pub struct HostFuture {
    msg_id: MessageId,
    finished: bool,
}

impl HostFuture {
    pub fn from_pollable(id: impl Into<PollableId>) -> Self {
        Self {
            msg_id: id.into(),
            finished: false,
        }
    }
}

impl Future for HostFuture {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
        assert!(!self.finished);
        if peek_response(self.msg_id) {
            self.finished = true;
            Poll::Ready(())
        } else {
            register_message_waker(self.msg_id, cx.waker().clone());
            Poll::Pending
        }
    }
}

/// If a response to this message ID has previously been obtained, extracts it for processing.
pub(crate) fn peek_response(msg_id: MessageId) -> bool {
    let mut state = STATE.lock();
    state.pending_messages.remove(&msg_id)
}

/// TODO: Resolve when the body is ready to be read? When we received header/request?
/// Maybe two futures - one for the code/headers and the other one for body?
#[pin_project]
#[derive(Debug)]
pub struct HttpFuture {
    #[pin] inner: HostFuture,
}

impl core::convert::TryFrom<HostFuture> for HttpFuture {
    type Error = HostFuture;
    fn try_from(value: HostFuture) -> Result<HttpFuture, HostFuture> {
        match value.msg_id.kind() {
            PollableKind::Http => Ok(HttpFuture { inner: value }),
            other => Err(value),
        }
    }
}

impl Future for HttpFuture {
    type Output = Result<HttpResponse, sp_core::offchain::HttpError>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
        use sp_core::offchain::HttpRequestId;
        use sp_core::offchain::HttpRequestStatus;
        use sp_core::offchain::HttpError;
        use core::convert::TryInto;

        let id: HttpRequestId = self.inner.msg_id.try_into()
            .expect("HttpFuture can be only constructed with HTTP HostFuture");
        let this = self.project();
        let inner = this.inner;

        match Future::poll(inner, cx) {
            Poll::Pending => Poll::Pending,
            Poll::Ready(()) => {
                let now = sp_io::offchain::timestamp();
                let status = sp_io::offchain::http_response_wait(&[id], Some(now));
                let code = match status.as_slice() {
                    &[HttpRequestStatus::Finished(code)] => code,
                    &[HttpRequestStatus::IoError] => return Poll::Ready(Err(HttpError::IoError)),
                    &[HttpRequestStatus::Invalid] => return Poll::Ready(Err(HttpError::Invalid)),
                    &[HttpRequestStatus::DeadlineReached] => {
                        // Internal logic error: We were signaled as ready but
                        // the request somehow internally timed out.
                        // Return an error instead of panicking
                        return Poll::Ready(Err(HttpError::IoError));
                    },
                    other => return Poll::Ready(Err(HttpError::Invalid)),
                };

                let headers = sp_io::offchain::http_response_headers(id);
                // TODO: Support chunked response
                // Ideally should piggy back on AsyncRead but we can't have sth
                // similar due to Cargo feature unification bug and `futures`
                // being compiled in `std` contexts in the dep graph
                let mut buf = [0u8; 1024];
                let len = match sp_io::offchain::http_response_read_body(id, &mut buf, Some(now)) {
                    Ok(read_len) => read_len,
                    // TODO: Needs more data, can't be handled as a single future as of now
                    Err(HttpError::DeadlineReached) => 0,
                    other => panic!("The state of the http request is finished, as checked above; qed"),
                };

                // TODO: Implement initial response buffering
                Poll::Ready(Ok(HttpResponse {
                    code,
                    headers,
                    body: buf[..len as usize].to_vec(),
                }))
            }
        }
    }
}

#[derive(Debug)]
pub struct HttpResponse {
    code: u16,
    headers: Vec<(Vec<u8>, Vec<u8>)>,
    body: Vec<u8>,
}
