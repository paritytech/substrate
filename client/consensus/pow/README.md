Proof of work consensus for Substrate.

To use this engine, you can need to have a struct that implements
`PowAlgorithm`. After that, pass an instance of the struct, along
with other necessary client references to `import_queue` to setup
the queue. Use the `start_mine` function for basic CPU mining.

The auxiliary storage for PoW engine only stores the total difficulty.
For other storage requirements for particular PoW algorithm (such as
the actual difficulty for each particular blocks), you can take a client
reference in your `PowAlgorithm` implementation, and use a separate prefix
for the auxiliary storage. It is also possible to just use the runtime
as the storage, but it is not recommended as it won't work well with light
clients.

License: GPL-3.0-or-later WITH Classpath-exception-2.0