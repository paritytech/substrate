Basic implementation of block-authoring logic.

# Example

```rust
// The first step is to create a `ProposerFactory`.
let mut proposer_factory = ProposerFactory::new(client.clone(), txpool.clone(), None);

// From this factory, we create a `Proposer`.
let proposer = proposer_factory.init(
	&client.header(&BlockId::number(0)).unwrap().unwrap(),
);

// The proposer is created asynchronously.
let proposer = futures::executor::block_on(proposer).unwrap();

// This `Proposer` allows us to create a block proposition.
// The proposer will grab transactions from the transaction pool, and put them into the block.
let future = proposer.propose(
	Default::default(),
	Default::default(),
	Duration::from_secs(2),
);

// We wait until the proposition is performed.
let block = futures::executor::block_on(future).unwrap();
println!("Generated block: {:?}", block.block);
```


License: GPL-3.0-or-later WITH Classpath-exception-2.0
