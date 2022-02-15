use futures::StreamExt;
use tokio_test::block_on;

use super::*;

mod normal_operation;
mod panicking_registry;

const TK: &str = "a_tracing_key";

type Message = u64;
type TestHub = Hub<Message, Registry>;
type TestReceiver = Receiver<Message, Registry>;

#[derive(Default)]
struct Registry {
	subscribers: HashMap<SeqID, SubsKey>,
}

struct SubsKey {
	_receiver: Option<TestReceiver>,
	panic: SubsKeyPanic,
}

impl SubsKey {
	fn new() -> Self {
		Self { _receiver: None, panic: SubsKeyPanic::None }
	}
	fn with_receiver(self, receiver: TestReceiver) -> Self {
		Self { _receiver: Some(receiver), ..self }
	}
	fn with_panic(self, panic: SubsKeyPanic) -> Self {
		Self { panic, ..self }
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SubsKeyPanic {
	None,

	OnSubscribePanicBefore,
	OnSubscribePanicAfter,

	OnUnsubscribePanicBefore,
	OnUnsubscribePanicAfter,

	OnDispatchPanicBefore,
	OnDispatchPanicAfter,
}

impl<M> Hub<M, Registry> {
	fn subs_count(&self) -> usize {
		self.map_registry_for_tests(|r| r.subscribers.len())
	}
	fn sink_count(&self) -> usize {
		self.shared.lock().borrow().sinks.len()
	}
}

impl Subscribe<SubsKey> for Registry {
	fn subscribe(&mut self, subs_key: SubsKey, subs_id: SeqID) {
		let sk_panic = subs_key.panic;

		if sk_panic == SubsKeyPanic::OnSubscribePanicBefore {
			panic!("on-subscribe-panic-before")
		}
		self.subscribers.insert(subs_id, subs_key);
		if sk_panic == SubsKeyPanic::OnSubscribePanicAfter {
			panic!("on-subscribe-panic-after")
		}
	}
}
impl Unsubscribe for Registry {
	fn unsubscribe(&mut self, subs_id: SeqID) {
		let sk_panic =
			self.subscribers.get(&subs_id).map(|sk| sk.panic).unwrap_or(SubsKeyPanic::None);

		if sk_panic == SubsKeyPanic::OnUnsubscribePanicBefore {
			panic!("on-unsubscribe-panic-before")
		}
		self.subscribers.remove(&subs_id);
		if sk_panic == SubsKeyPanic::OnUnsubscribePanicAfter {
			panic!("on-unsubscribe-panic-after")
		}
	}
}
impl Dispatch<Message> for Registry {
	type Item = Message;
	type Ret = ();

	fn dispatch<F>(&mut self, message: Message, mut dispatch: F) -> Self::Ret
	where
		F: FnMut(&SeqID, Self::Item),
	{
		self.subscribers.iter().for_each(|(id, subs_key)| {
			if subs_key.panic == SubsKeyPanic::OnDispatchPanicBefore {
				panic!("on-dispatch-panic-before")
			}
			dispatch(id, message);
			if subs_key.panic == SubsKeyPanic::OnDispatchPanicAfter {
				panic!("on-dispatch-panic-after")
			}
		});
	}
}
