# The `benchmark machine` command

Different Substrate chains can have different hardware requirements.  
It is therefore important to be able to quickly gauge if a piece of hardware fits a chains' requirements.  

The `benchmark machine` command archives this by measuring key metrics and making them comparable.  
Invoking the command looks like this (for debugging you can use `--profile=release`):  
```sh
cargo run --profile=production -- benchmark machine --dev
```

## Output

The output from the invocation on reference hardware above:  

```pre
+----------+----------------+-------+------+
| Category | Function       | Score | Unit |
+----------+----------------+-------+------+
| CPU      | BLAKE2-256     | 1029  | MB/s |
+----------+----------------+-------+------+
| CPU      | SR25519 Verify | 665.3 | KB/s |
+----------+----------------+-------+------+
| Memory   | Copy           | 14697 | MB/s |
+----------+----------------+-------+------+
| Disk     | Seq Write      | 472   | MB/s |
+----------+----------------+-------+------+
| Disk     | Rnd Write      | 212   | MB/s |
+----------+----------------+-------+------+
```

The *category* indicate which part of the hardware is mainly used:  
- **CPU** Processor intensive task
- **Memory** RAM intensive task
- **Disk** Hard drive intensive task.

The *function* is the concrete benchmark that was run:  
- **BLAKE2-256** The throughput of the [Blake2-256] cryptographic hashing function with 32 KiB input. The [blake2_256 function] is used in many places. The throughput of a hash function strongly depends on the input size, therefore we settled to use a fixed input size for comparable results.
- **SR25519 Verify** [sr25519] is an optimized version of the [Curve25519] signature scheme. Signatures are used by Substrate when verifying extrinsics and blocks.
- **Copy** The throughput of copying memory from one place in the RAM to another.
- **Seq Write** The throughput of writing data to the storage location sequentially. It is important that the same disk is used that will later-on be used to store the chain data. See [--base-path] below.
- **Rnd Write** The throughput of writing data to the storage location in a random order. This is normally much slower than the sequential write since.

The *score* is the average result of each benchmark which.  
It always adheres to "higher is better".  

## Interpretation

TODO

## Arguments

- `--verify-duration` How long the verification benchmark should run.
- `--chain` / `--dev` Specify the chain config to use. This will be used to compare the results with the requirements of the chain (WIP).
- `--base-path` The location on the disk that should be used for the disk benchmarks. You can try this on different disks or even on a mounted RAM-disk. It is important to use the same location that will later-on be used to store the chain data to get the correct results.

# Future

TODO add issue link

<!-- LINKS -->
[Blake2-256]: https://www.blake2.net/
[blake2_256 function]: https://crates.parity.io/sp_core/hashing/fn.blake2_256.html
[ed25519]: https://ed25519.cr.yp.to/
