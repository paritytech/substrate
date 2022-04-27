# Shared code

Contains code that is shared among multiple sub-commands.

## Arguments

- `--mul` Multiply the result with a factor. Can be used to manually adjust for future chain growth.
- `--add` Add a value to the result. Can be used to manually offset the results.
- `--metric` Set the metric to use for calculating the final weight from the raw data. Defaults to `average`.
- `--weight-path` Set the file or directory to write the weight files to.
- `--db` The database backend to use. This depends on your snapshot.
- `--pruning` Set the pruning mode of the node. Some benchmarks require you to set this to `archive`.
- `--base-path` The location on the disk that should be used for the benchmarks. You can try this on different disks or even on a mounted RAM-disk. It is important to use the same location that will later-on be used to store the chain data to get the correct results.

License: Apache-2.0
