Substrate offchain workers.

The offchain workers is a special function of the runtime that
gets executed after block is imported. During execution
it's able to asynchronously submit extrinsics that will either
be propagated to other nodes or added to the next block
produced by the node as unsigned transactions.

Offchain workers can be used for computation-heavy tasks
that are not feasible for execution during regular block processing.
It can either be tasks that no consensus is required for,
or some form of consensus over the data can be built on-chain
for instance via:
1. Challenge period for incorrect computations
2. Majority voting for results
3. etc

License: GPL-3.0-or-later WITH Classpath-exception-2.0