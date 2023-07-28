# Transaction Storage Pallet

Indexes transactions and manages storage proofs.

Allows storing arbitrary data on the chain. Data is automatically removed after `StoragePeriod` blocks, unless the storage is renewed.
Validators must submit proof of storing a random chunk of data for block `N - StoragePeriod` when producing block `N`.

# Running a chain

The following describes how to set up a new storage chain.

Start with generating a chain spec.

```bash
cargo run --release -- build-spec --chain=local > sc_init.json
```

Edit the json chain spec file to customise the chain. The storage chain genesis params are configured in the `transactionStorage` section.
Note that `storagePeriod` is specified in blocks and changing it also requires code changes at the moment.

Build a raw spec from the init spec.

```bash
cargo run --release build-spec --chain=sc_init.json --raw > sc.json
```

Run a few validator nodes.

```bash
cargo run --release -- --chain=sc.json -d /tmp/alice --storage-chain --keep-blocks=100800 --ipfs-server --validator --alice
cargo run --release -- --chain=sc.json -d /tmp/bob --storage-chain --keep-blocks=100800 --ipfs-server --validator --bob
```

`--storage-chain` enables transaction indexing.
`--keep-blocks=100800` enables block pruning. The value here should be greater or equal than the storage period.
`--ipfs-server` enables serving stored content over IPFS.

Once the network is started, any other joining nodes need to sync with `--sync=fast`. Regular sync will fail because block pruning removes old blocks. The chain does not keep full block history.

```bash
cargo run --release -- --chain=sc.json -d /tmp/charlie --storage-chain --keep-blocks=100800 --ipfs-server --validator --charlie --sync=fast
```

# Making transactions

To store data use the `transactionStorage.store` extrinsic. And IPFS CID can be generated from the Blake2-256 hash of the data.

```js
const util_crypto = require('@polkadot/util-crypto');
const keyring_api = require('@polkadot/keyring');
const polkadot_api = require('@polkadot/api');
const fs = require('fs');
const multihash = require('multihashes');
const CID = require('cids')

const wsProvider = new polkadot_api.WsProvider();
const api = await polkadot_api.ApiPromise.create({ provider: wsProvider });

const keyring = new keyring_api.Keyring({ type: "sr25519" });
const alice = keyring.addFromUri("//Alice");

const file = fs.readFileSync('cute_kitten.jpeg');
const hash = util_crypto.blake2AsU8a(file)
const encoded_hash = multihash.encode(hash, 'blake2b-256');

const cid = new CID(1, 'blake2b-256', encoded_hash)
console.log(cid.toString());

const txHash = await api.tx.transactionStorage.store('0x' + file.toString('hex')).signAndSend(alice);
```
Data can be queried over IPFS

```bash
ipfs swarm connect <substrate peer address>
ipfs block get /ipfs/<CID> > kitten.jpeg
```

To renew data and prevent it from being disposed after the storage period, use `transactionStorage.renew(block, index)`
where `block` is the block number of the previous store or renew transction, and index is the index of that transaction in the block.


License: Apache-2.0
