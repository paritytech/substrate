# Shared code

Contains code that is shared among multiple sub-commands.

## Arguments
- `--mul` Multiply the result with a factor. Can be used to manually adjust for future chain growth.
- `--add` Add a value to the result. Can be used to manually offset the results.
- `--metric` Set the metric to use for calculating the final weight from the raw data. Defaults to `average`.
- `--weight-path` Set the file or directory to write the weight files to.
