use std::{
	collections::HashMap,
	pin::Pin,
	sync::{Arc, Weak},
	task::{Context, Poll},
};

use ::futures::stream::{FusedStream, Stream};
use ::parking_lot::Mutex;

pub mod channels;

pub type SubsID = crate::id_sequence::SeqID;

pub trait Channel {
	type Tx;
	type Rx;
	type Item;

	fn create(&self) -> (Self::Tx, Self::Rx);
	fn send(&self, tx: &mut Self::Tx, item: Self::Item);
}

pub trait Unsubscribe {
	fn unsubscribe(&mut self, subs_id: &SubsID);
}

pub trait Subscribe<K> {
	fn subscribe(&mut self, subs_key: K, subs_id: SubsID);
}

pub trait Dispatch<K> {
	type Item;
	fn dispatch<F>(&mut self, disp_key: K, dispatch: F)
	where
		F: FnMut(&SubsID, Self::Item);
}

#[derive(Debug)]
pub struct Hub<Ch, R>
where
	Ch: Channel,
{
	channel: Ch,
	shared: Arc<Mutex<Shared<R, Ch::Tx>>>,
}

#[derive(Debug)]
pub struct Receiver<Ch, R>
where
	Ch: Channel,
	R: Unsubscribe,
{
	// NB: this field should be defined before `rx`.
	// (The fields of a struct are dropped in declaration order.)[https://doc.rust-lang.org/reference/destructors.html]
	_unsubs_guard: UnsubscribeGuard<R, Ch::Tx>,

	// NB: this field should be defined after `_unsubs_guard`.
	rx: Ch::Rx,
}

#[derive(Debug)]
struct UnsubscribeGuard<R, Tx>
where
	R: Unsubscribe,
{
	shared: Weak<Mutex<Shared<R, Tx>>>,
	subs_id: SubsID,
}

#[derive(Debug)]
struct Shared<R, Tx> {
	id_sequence: crate::id_sequence::IDSequence,
	registry: R,
	sinks: HashMap<SubsID, Tx>,
}

impl<R, Tx> Drop for UnsubscribeGuard<R, Tx>
where
	R: Unsubscribe,
{
	fn drop(&mut self) {
		if let Some(shared) = self.shared.upgrade() {
			shared.lock().unsubscribe(&self.subs_id);
		}
	}
}

impl<Ch, Tx, R> Hub<Ch, R>
where
	Ch: Channel<Tx = Tx>,
{
	pub fn new(channel: Ch) -> Self
	where
		R: Default,
	{
		Self::new_with_registry(channel, Default::default())
	}

	pub fn new_with_registry(channel: Ch, registry: R) -> Self {
		let shared =
			Shared { registry, sinks: Default::default(), id_sequence: Default::default() };
		let shared = Arc::new(Mutex::new(shared));
		Self { channel, shared }
	}

	pub fn subscribe<K>(&self, subs_key: K) -> Receiver<Ch, R>
	where
		R: Subscribe<K> + Unsubscribe,
	{
		let mut shared = self.shared.lock();

		let subs_id = shared.id_sequence.next_id();
		let (tx, rx) = self.channel.create();
		assert!(shared.sinks.insert(subs_id, tx).is_none(), "Used IDSequence to create another ID. Should be unique until u64 is overflowed. Should be unique.");
		shared.registry.subscribe(subs_key, subs_id);

		let unsubs_guard = UnsubscribeGuard { shared: Arc::downgrade(&self.shared), subs_id };
		Receiver { _unsubs_guard: unsubs_guard, rx }
	}

	pub fn dispatch<K>(&self, disp_key: K)
	where
		R: Dispatch<K, Item = Ch::Item>,
	{
		let mut shared = self.shared.lock();
		let (registry, sinks) = shared.get_mut();

		registry.dispatch(disp_key, |subs_id, item| {
			if let Some(tx) = sinks.get_mut(&subs_id) {
				self.channel.send(tx, item)
			} else {
				// log::warn!(
				//     "{} as Dispatch<{}>::dispatch(...). No Sink for SubsID = {}",
				//     std::any::type_name::<R>(),
				//     std::any::type_name::<K>(),
				//     subs_id
				// );
			}
		});
	}
}

impl<R, Tx> Shared<R, Tx> {
	fn get_mut(&mut self) -> (&mut R, &mut HashMap<SubsID, Tx>) {
		(&mut self.registry, &mut self.sinks)
	}

	fn unsubscribe(&mut self, subs_id: &SubsID)
	where
		R: Unsubscribe,
	{
		self.registry.unsubscribe(subs_id);
		self.sinks.remove(subs_id);
	}
}

impl<Ch, R> Clone for Hub<Ch, R>
where
	Ch: Channel + Clone,
{
	fn clone(&self) -> Self {
		Self { channel: self.channel.clone(), shared: self.shared.clone() }
	}
}

impl<Ch, R> Unpin for Receiver<Ch, R>
where
	Ch: Channel,
	R: Unsubscribe,
{
}

impl<Ch, R> Stream for Receiver<Ch, R>
where
	Ch: Channel,
	R: Unsubscribe,
	Ch::Rx: Stream + Unpin,
{
	type Item = <Ch::Rx as Stream>::Item;

	fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
		Pin::new(&mut self.get_mut().rx).poll_next(cx)
	}
}

impl<Ch, R> FusedStream for Receiver<Ch, R>
where
	Ch: Channel,
	R: Unsubscribe,
	Ch::Rx: FusedStream + Unpin,
{
	fn is_terminated(&self) -> bool {
		self.rx.is_terminated()
	}
}
