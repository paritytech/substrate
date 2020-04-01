use super::{SendError, Sender};
use futures_core::task::{Context, Poll};
use futures_sink::Sink;
use std::pin::Pin;

impl<T> Sink<T> for Sender<T> {
    type Error = SendError;

    fn poll_ready(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Result<(), Self::Error>> {
        (*self).poll_ready(cx)
    }
 
    fn start_send(
        mut self: Pin<&mut Self>,
        msg: T,
    ) -> Result<(), Self::Error> {
        (*self).start_send(msg)
    }

    fn poll_flush(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Result<(), Self::Error>> {
        match (*self).poll_ready(cx) {
            Poll::Ready(Err(ref e)) if e.is_disconnected() => {
                // If the receiver disconnected, we consider the sink to be flushed.
                Poll::Ready(Ok(()))
            }
            x => x,
        }
    }

    fn poll_close(
        mut self: Pin<&mut Self>,
        _: &mut Context<'_>,
    ) -> Poll<Result<(), Self::Error>> {
        self.disconnect();
        Poll::Ready(Ok(()))
    }
}
