# sc-telemetry

To start using this module, please initialize the global logger from `sc-tracing`. This will
return a [`TelemetryWorker`] which can be used to register substrate node. In order to do that,
first call [`TelemetryWorker::handle()`] to get a handle to the worker, then use
[`TelemetryHandle::start_telemetry()`] to initialize the telemetry. This will also return a
[`TelemetryConnectionNotifier`] which can be used to create streams of events for whenever the
connection to a telemetry server is (re-)established.

The macro [`telemetry`] can be used to report telemetries from anywhere in the code but the
telemetry must have been initialized through [`TelemetryHandle::start_telemetry()`].
Initializing the telemetry will make all the following code execution (including newly created
async background tasks) report the telemetries through the endpoints provided during the
initialization. If multiple telemetries have been started, the latest one (higher up in the
stack) will be used. If no telemetry has been started, nothing will be reported.

License: GPL-3.0-or-later WITH Classpath-exception-2.0
