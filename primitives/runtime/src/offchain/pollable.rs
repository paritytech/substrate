//! A simple futures executor/reactor used in tandem with host-driven futures.
//!
//! At the time of writing, the off-chain workers are not capable of network I/O
//! or background scheduling on their own. To work around that, they need
//! to schedule the work on the host side via runtime-called functions which can
//! be later polled from runtime for completion using the [`PollableId`] handle
//! via the low-level [`sp_io::offchain::pollable_wait`] API.
//!
//! ## Architecture
//! The current implementation uses both an executor (used to spawn and executing
//! tasks) and a reactor (notifies tasks when it's possible to make further progress)
//! on the host side **and** and a simple single-threaded executor/reactor
//! on the runtime side (which is documented here).
//!
//! Most of the heavy lifting is done on the host side such as scheduling timers
//! or performing network I/O, while the simple executor/reactor here is mostly
//! to conveniently interface with this, enabling niceties like async/await
//! syntax sugar or future combinators.
//!
//! Because of this approach, the following `Future`s are supported here:
//! 1. immediately ready ones (i.e. which return `Poll::Ready`),
//! 2. internally host-driven ones via `PollableId`,
//! 3. combinators for the supported futures.

// Based on https://github.com/tomaka/redshirt/blob/802e4ab44078e15b47dc72afc6b7e45bab1b72df/interfaces/syscalls/src/block_on.rs#L88.

#![allow(dead_code, unused_variables)]

use sp_core::offchain::{PollableId, PollableKind};
use sp_core::offchain::{HttpError, HttpRequestId, HttpRequestStatus};
use sp_std::{rc::Rc, collections::btree_set::BTreeSet};
use sp_std::prelude::*;

use core::cell::RefCell;
use core::convert::{TryFrom, TryInto};
use core::future::Future;
use core::mem::{self, ManuallyDrop};
use core::pin::Pin;
use core::task::{self, Context, Poll, Waker, RawWaker, RawWakerVTable};

use spin::Mutex;
use pin_project::pin_project;

pub(crate) type MessageId = PollableId;

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

/// Block until a given future is resolved.
///
/// ## Support
/// At the time of writing, the only supported futures are ones that:
/// 1. are immediately ready (i.e. return `Poll::Ready`),
/// 2. can be driven by the host via the underlying low-level [`PollableId`] API,
/// 3. are a combination of the above (e.g. `futures::future::join`ed).
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
		// We poll the future continuously until it is either Ready,
		// or the waker stops being invoked during the polling.
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

impl<T> From<T> for HostFuture where T: Into<PollableId> {
	fn from(value: T) -> HostFuture {
		Self {
			msg_id: value.into(),
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

/// Future that resolves to a HTTP request response.
///
/// Because HTTP response can be chunked, the resolved [`HttpResponse`] contains
/// both HTTP status code and headers but the [`HttpResponse::body`] is a future
/// type that has to be driven separately.
#[pin_project]
#[derive(Debug)]
pub struct HttpFuture {
	#[pin] inner: HostFuture,
}

impl TryFrom<HostFuture> for HttpFuture {
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
		let id: HttpRequestId = self.inner.msg_id.try_into()
			.expect("HttpFuture can be only constructed with HTTP HostFuture");

		match Future::poll(self.project().inner, cx) {
			Poll::Pending => return Poll::Pending,
			Poll::Ready(()) => {},
		}

		let now = sp_io::offchain::timestamp();
		let status = sp_io::offchain::http_response_wait(&[id], Some(now));

		let code = match status.as_slice() {
			[HttpRequestStatus::Finished(code)] => *code,
			[HttpRequestStatus::IoError] => return Poll::Ready(Err(HttpError::IoError)),
			[HttpRequestStatus::Invalid] => return Poll::Ready(Err(HttpError::Invalid)),
			[HttpRequestStatus::DeadlineReached] => {
				// Internal logic error: We were signaled as ready but
				// the request somehow internally timed out.
				// Return an error instead of panicking
				return Poll::Ready(Err(HttpError::IoError));
			},
			[] | [_, _, ..] => unreachable!("waiting for a single ID should give exactly one; qed"),
		};

		let headers = sp_io::offchain::http_response_headers(id);

		Poll::Ready(Ok(HttpResponse {
			code,
			headers,
			body: HttpBodyFuture {
				id,
				buf: Some(vec![0; 1024]),
				len: 0,
			},
		}))
	}
}


/// A future type that resolves to an HTTP response body.
///
/// Part of the [`HttpResponse`] value.
#[derive(Debug)]
pub struct HttpBodyFuture {
	id: HttpRequestId,
	buf: Option<Vec<u8>>,
	len: usize,
}

impl Future for HttpBodyFuture {
	type Output = Box<[u8]>;

	fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		// Help the borrow checker see disjoint field mutable borrow through Pin
		let this = &mut *self;
		let (id, len) = (this.id, &mut this.len);
		let self_buf = this.buf.as_mut().expect("HttpBodyFuture polled after value taken");

		loop {
			let buf = &mut self_buf[*len..];
			// Ensure that we can always write something, so that reading 0 bytes
			// means EOF rather than inability to write more
			debug_assert_ne!(buf.len(), 0);

			// Read body in a non-blocking fashion with present timestamp as deadline
			let now = sp_io::offchain::timestamp();
			match sp_io::offchain::http_response_read_body(id, buf, Some(now)) {
				Ok(0) => {
					let mut buf = this.buf.take()
						.expect("HttpBodyFuture polled after value taken");
					buf.truncate(*len);

					return Poll::Ready(buf.into_boxed_slice());
				},
				Ok(bytes_read) => {
					// Grow the temporary buffer if it's full
					if bytes_read as usize == buf.len() {
						let growth = self_buf.len() / 2 * 3; // 1.5
						let new_len = self_buf.len() + growth;
						self_buf.resize_with(new_len, Default::default);
					}
					*len += bytes_read as usize;

					continue;
				},
				Err(HttpError::DeadlineReached) => {
					let fut = HostFuture::from(id);
					pin_mut!(fut);
					if let Poll::Ready(()) = fut.poll(cx) {
						// More work is ready by now, reschedule to poll again
						cx.waker().wake_by_ref();
					}

					return Poll::Pending;
				},
				Err(HttpError::IoError) | Err(HttpError::Invalid) => panic!(
					"HttpBodyFuture is created for HTTP requests that are Finished \
					and so reading body can return DeadlineReached at worst; qed"
				),
			}
		}
	}
}

/// The output type for the [`HttpFuture`] future.
///
/// Because HTTP response can be chunked, the HTTP status code and headers are
/// immediately available but the response body needs to be driven separately.
#[derive(Debug)]
pub struct HttpResponse {
	pub code: u16,
	pub headers: Vec<(Vec<u8>, Vec<u8>)>,
	pub body: HttpBodyFuture,
}
