Telemetry utilities.

Calling `init_telemetry` registers a global `slog` logger using `slog_scope::set_global_logger`.
After that, calling `slog_scope::with_logger` will return a logger that sends information to
the telemetry endpoints. The `telemetry!` macro is a short-cut for calling
`slog_scope::with_logger` followed with `slog_log!`.

Note that you are supposed to only ever use `telemetry!` and not `slog_scope::with_logger` at
the moment. Substrate may eventually be reworked to get proper `slog` support, including sending
information to the telemetry.

The [`Telemetry`] struct implements `Stream` and must be polled regularly (or sent to a
background thread/task) in order for the telemetry to properly function. Dropping the object
will also deregister the global logger and replace it with a logger that discards messages.
The `Stream` generates [`TelemetryEvent`]s.

> **Note**: Cloning the [`Telemetry`] and polling from multiple clones has an unspecified behaviour.

# Example

```rust
use futures::prelude::*;

let telemetry = sc_telemetry::init_telemetry(sc_telemetry::TelemetryConfig {
	endpoints: sc_telemetry::TelemetryEndpoints::new(vec![
		// The `0` is the maximum verbosity level of messages to send to this endpoint.
		("wss://example.com".into(), 0)
	]).expect("Invalid URL or multiaddr provided"),
	// Can be used to pass an external implementation of WebSockets.
	wasm_external_transport: None,
});

// The `telemetry` object implements `Stream` and must be processed.
std::thread::spawn(move || {
	futures::executor::block_on(telemetry.for_each(|_| future::ready(())));
});

// Sends a message on the telemetry.
sc_telemetry::telemetry!(sc_telemetry::SUBSTRATE_INFO; "test";
	"foo" => "bar",
)
```


License: GPL-3.0-or-later WITH Classpath-exception-2.0