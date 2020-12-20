Custom panic hook with bug report link

This crate provides the [`set`] function, which wraps around [`std::panic::set_hook`] and
sets up a panic hook that prints a backtrace and invites the user to open an issue to the
given URL.

By default, the panic handler aborts the process by calling [`std::process::exit`]. This can
temporarily be disabled by using an [`AbortGuard`].

License: Apache-2.0