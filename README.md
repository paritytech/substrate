Example timing (simple transfer):

```
2020-04-15 16:04:43.681 txpool-verifier0 INFO sc_transaction_pool::api  ValidateTransaction: check version: 37599ns
2020-04-15 16:04:43.681 txpool-verifier0 TRACE frame_executive  ValidateTransaction: start
2020-04-15 16:04:43.681 txpool-verifier0 TRACE frame_executive  ValidateTransaction: start/native
2020-04-15 16:04:43.681 txpool-verifier0 TRACE frame_executive  ValidateTransaction: encoded
2020-04-15 16:04:43.681 txpool-verifier0 TRACE frame_executive  ValidateTransaction: encoded (19239 ns)
2020-04-15 16:04:43.681 txpool-verifier0 TRACE frame_executive  ValidateTransaction: checked
2020-04-15 16:04:43.681 txpool-verifier0 TRACE frame_executive  ValidateTransaction: checked (108819 ns)
2020-04-15 16:04:43.681 txpool-verifier0 TRACE frame_executive  ValidateTransaction: dispatchinfo
2020-04-15 16:04:43.681 txpool-verifier0 TRACE frame_executive  ValidateTransaction: dispatchinfo (116528 ns)
2020-04-15 16:04:43.681 txpool-verifier0 TRACE frame_executive  ValidateTransaction: done
2020-04-15 16:04:43.681 txpool-verifier0 TRACE frame_executive  ValidateTransaction: done (137791 ns)
2020-04-15 16:04:43.681 txpool-verifier0 INFO sc_transaction_pool::api  ValidateTransaction: took: 305684ns
```

```
2020-04-15 16:04:31.13 txpool-verifier1 INFO sc_transaction_pool::api  ValidateTransaction: check version: 62429ns
2020-04-15 16:04:31.13 txpool-verifier1 TRACE frame_executive  ValidateTransaction: start
2020-04-15 16:04:31.13 txpool-verifier1 TRACE frame_executive  ValidateTransaction: start/native
2020-04-15 16:04:31.13 txpool-verifier1 TRACE frame_executive  ValidateTransaction: encoded
2020-04-15 16:04:31.13 txpool-verifier1 TRACE frame_executive  ValidateTransaction: encoded (27385 ns)
2020-04-15 16:04:31.13 txpool-verifier1 TRACE frame_executive  ValidateTransaction: checked
2020-04-15 16:04:31.13 txpool-verifier1 TRACE frame_executive  ValidateTransaction: checked (173238 ns)
2020-04-15 16:04:31.13 txpool-verifier1 TRACE frame_executive  ValidateTransaction: dispatchinfo
2020-04-15 16:04:31.13 txpool-verifier1 TRACE frame_executive  ValidateTransaction: dispatchinfo (183297 ns)
2020-04-15 16:04:31.13 txpool-verifier1 TRACE frame_executive  ValidateTransaction: done
2020-04-15 16:04:31.13 txpool-verifier1 TRACE frame_executive  ValidateTransaction: done (221605 ns)
2020-04-15 16:04:31.13 txpool-verifier1 INFO sc_transaction_pool::api  ValidateTransaction: took: 482321ns
```


# Substrate &middot; [![GitHub license](https://img.shields.io/github/license/paritytech/substrate)](LICENSE) [![GitLab Status](https://gitlab.parity.io/parity/substrate/badges/master/pipeline.svg)](https://gitlab.parity.io/parity/substrate/pipelines) [![PRs Welcome](https://img.shields.io/badge/PRs-welcome-brightgreen.svg)](docs/CONTRIBUTING.adoc)

Substrate is a next-generation framework for blockchain innovation.

## Trying it out

Simply go to [substrate.dev](https://substrate.dev) and follow the [getting started](https://substrate.dev/docs/en/overview/getting-started/) instructions.

## Contributions & Code of Conduct

Please follow the contributions guidelines as outlined in [`docs/CONTRIBUTING.adoc`](docs/CONTRIBUTING.adoc). In all communications and contributions, this project follows the [Contributor Covenant Code of Conduct](docs/CODE_OF_CONDUCT.adoc).

## Security

The security policy and procedures can be found in [`docs/SECURITY.md`](docs/SECURITY.md).

## License

Substrate is [GPL 3.0 licensed](LICENSE).
