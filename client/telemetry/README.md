# sc-telemetry

To start using this module, please initialize the global logger from `sc-tracing`. This will
return a [`TelemetryWorker`] which can be used to register substrate node. In order to do that,
first call [`TelemetryWorker::handle()`] to get a handle to the worker, then call
[`TelemetrySpan::new()`] to create a new span, then use [`TelemetryHandle::start_telemetry()`]
to initialize the telemetry. This will also return a [`TelemetryConnectionNotifier`] which can
be used to create streams of events for whenever the connection to a telemetry server is
(re-)established.

The macro [`telemetry`] can be used to report telemetries from anywhere in the code but the
telemetry must have been initialized through [`TelemetryHandle::start_telemetry()`].

The telemetry span needs to be passed to the [`sc_service::TaskManager`] in order to make all
the async background tasks report the telemetries through the endpoints provided during the
initialization.

License: GPL-3.0-or-later WITH Classpath-exception-2.0
