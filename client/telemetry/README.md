# sc-telemetry

Substrate's client telemetry is a part of substrate that allows ingesting telemetry data
with for example [Polkadot telemetry](https://github.com/paritytech/substrate-telemetry).

It works using Tokio's [tracing](https://github.com/tokio-rs/tracing/) library. The telemetry
information uses tracing's logging to report the telemetry data which is then retrieved by a
tracing `Layer`. This layer will then send the data through an asynchronous channel to a
background task called [`TelemetryWorker`] which will send the information to the configured
remote telemetry servers.

If multiple substrate nodes are running in the same process, it uses a `tracing::Span` to
identify which substrate node is reporting the telemetry. Every task spawned using sc-service's
`TaskManager` automatically inherit this span.

Substrate's nodes initialize/register with the [`TelemetryWorker`] using a [`TelemetryHandle`].
This handle can be cloned and passed around. It uses an asynchronous channel to communicate with
the running [`TelemetryWorker`] dedicated to registration. Registering can happen at any point
in time during the process execution.

License: GPL-3.0-or-later WITH Classpath-exception-2.0
