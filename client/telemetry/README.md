# sc-telemetry

Telemetry utilities.

The `Telemetry` object is a `Stream` that needs to be polled regularly in order to function.
It is unregistered when the object is dropped.

`Telemetry` objects can be created through its constructor `Telemetry::new()`, or through a
`Telemetries` instance. The difference between the two is that `Telemetries` will re-use
connections to the same server if possible and manages a collection of channel `Sender` for you
(see `Senders`). `Telemetries` should be used unless you need finer control.

The macro `telemetry!` can be used to report telemetries from anywhere but a `Telemetry` must
have been initialized. Creating a `Telemetry` will make all the following code execution use
this `Telemetry` when reporting with the macro `telemetry!` until the `Telemetry` object is
dropped. If multiple `Telemetry` objects are created, the latest one (higher up in the stack)
will be used. If no `Telemetry` object can be found, nothing happens.

The [`Telemetry`] struct implements `Stream` and must be polled regularly (or sent to a
background thread/task) in order for the telemetry to properly function. Dropping the object
will also deregister the global logger and replace it with a logger that discards messages.
The `Stream` generates [`TelemetryEvent`]s.

License: GPL-3.0-or-later WITH Classpath-exception-2.0
