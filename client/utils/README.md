# Utilities Primitives for Substrate

This crate provides `mpsc::tracing_unbounded` function that returns wrapper types to
`async_channel::Sender<T>` and `async_channel::Receiver<T>`, which register every
`send`/`received`/`dropped` action happened on the channel.

Also this wrapper creates and registers a prometheus vector with name `unbounded_channel_len`
and labels:

| Label        | Description                                   |
| ------------ | --------------------------------------------- |
| entity       | Name of channel passed to `tracing_unbounded` |
| action       | One of `send`/`received`/`dropped`            |

License: Apache-2.0
