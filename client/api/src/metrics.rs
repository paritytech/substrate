
use lazy_static::lazy_static;
use parking_lot::RwLock;
use std::collections::HashMap;
use futures::channel::mpsc::{self, UnboundedReceiver, UnboundedSender, TryRecvError, TrySendError};
use futures::{task::{Poll, Context}, stream::Stream};
use std::pin::Pin;

lazy_static! {
    pub static ref GLOBAL_METRICS: InternalMetrics = InternalMetrics::new();
}

pub struct InternalMetrics {
    metrics: RwLock<HashMap<&'static str, u64>>
}

impl InternalMetrics {
    pub fn new() -> Self {
        Self {
            metrics: RwLock::new(HashMap::new())
        }
    }

    pub fn incr(&self, key: &'static str) {
        self.incr_by(key, 1)
    }

    pub fn incr_by(&self, key: &'static str, value: u64) {
        let mut h = self.metrics.write();
        h.entry(key)
            .and_modify(|v| {
                *v = v.checked_add(value).unwrap_or(u64::MAX)
            })
            .or_insert(value);
    }

    pub fn decr(&self, key: &'static str) {
        self.decr_by(key, 1);
    }

    pub fn decr_by(&self, key: &'static str, value: u64) {
        let mut h = self.metrics.write();
        h.entry(key)
            .and_modify(|v| {
                *v = v.checked_sub(value).unwrap_or(0)
            })
            .or_insert(0);
    }

    pub fn set(&self, key: &'static str, value: u64) {
        self.metrics.write().insert(key, value);
    }

    pub fn get(&self, key: &'static str) -> Option<u64> {
        self.metrics.read().get(key).cloned()
    }

    pub fn inner<'a>(&'a self) -> &'a RwLock<HashMap<&'static str, u64>> {
        &self.metrics
    }
}

#[derive(Clone, Debug)]
pub struct TracingUnboundedSender<T>(&'static str, UnboundedSender<T>);
#[derive(Debug)]
pub struct TracingUnboundedReceiver<T>(&'static str, UnboundedReceiver<T>);

impl<T> TracingUnboundedSender<T> {
    pub fn unbounded_send(&self, msg: T) -> Result<(), TrySendError<T>> {
        self.1.unbounded_send(msg).map(|s|{
            GLOBAL_METRICS.incr(self.0);
            s
        })
    }
}

impl<T> TracingUnboundedReceiver<T> {
    pub fn try_next(&mut self) -> Result<Option<T>, TryRecvError> {
        self.1.try_next().map(|s| {
            if s.is_some() {
                GLOBAL_METRICS.decr(self.0);
            }
            s
        })
    }
}

impl<T> Drop for TracingUnboundedReceiver<T> {
    fn drop(&mut self) {
        let mut count = 0;
        // consume
        while let Ok(Some(..)) = self.try_next() {
            count += 1;
        }

        // and discount the messages
        if count > 0 {
            GLOBAL_METRICS.decr_by(self.0, count);
        }
    }
}

impl<T> Unpin for TracingUnboundedReceiver<T> {}

impl<T> Stream for TracingUnboundedReceiver<T> {
    type Item = T;

    fn poll_next(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Option<T>> {
        let s = self.get_mut();
        match Pin::new(&mut s.1).poll_next(cx) {
            Poll::Ready(msg) => {
                if msg.is_some() {
                    GLOBAL_METRICS.decr(s.0);
                }
                Poll::Ready(msg)
            }
            Poll::Pending => {
                Poll::Pending
            }
        }
    }
}

pub fn tracing_unbounded<T>(key: &'static str) ->(TracingUnboundedSender<T>, TracingUnboundedReceiver<T>) {
    let (s, r) = mpsc::unbounded();
    (TracingUnboundedSender(key.clone(), s), TracingUnboundedReceiver(key,r))
}