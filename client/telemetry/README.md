# sc-telemetry

Substrate's client telemetry is a part of substrate that allows logging telemetry information
with a [Polkadot telemetry](https://github.com/paritytech/substrate-telemetry).

It works using Tokio's [tracing](https://github.com/tokio-rs/tracing/). The telemetry
information uses tracing's logging to report the telemetry which is then retrieved by a
tracing's `Layer`. This layer will then send the data through an asynchronous channel and to a
background task called [`TelemetryWorker`] which will send the information to the telemetry
server.

If multiple substrate nodes are running, it uses a tracing's `Span` to identify which substrate
node is reporting the telemetry. Every task spawned using sc-service's `TaskManager`
automatically inherit this span.

License: GPL-3.0-or-later WITH Classpath-exception-2.0
