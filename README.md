# Cere Node with PoS consensus

## How to become a validator

Follow the [instructions](https://github.com/Cerebellum-Network/validator-instructions#how-to-become-a-validator) to get the Node up and running.

## License

- Cere Primitives (`sp-*`), Frame (`frame-*`) and the pallets (`pallets-*`), binaries (`/bin`) and all other utilities are licensed under [Apache 2.0](LICENSE-APACHE2).
- Cere Client (`/client/*` / `sc-*`) is licensed under [GPL v3.0 with a classpath linking exception](LICENSE-GPL3).

## Build the node

1. [Install `Docker`](https://docs.docker.com/get-docker/).
2. Run the following command to update submodules.

```
 git submodule update --init --recursive
```

3. Run the following command to build the node.

```
 docker build .
```

## Extract wasm file
1. Run the following command to extract wasm from image.

```
 bash scripts/extract-wasm.sh node_runtime_artifacts_directory image_tag
```
## Run tests

1. [Install `Docker`](https://docs.docker.com/get-docker/).
2. Run the following command run tests.

```
 docker build --build-arg ECR_REGISTRY=$ECR_REGISTRY -f Dockerfile.tests -t pos-network-node:test .
```

3. Run the following command to copy SC artifacts to test_data folder.

```
id=$(docker create $ECR_REGISTRY/ddc-smart-contract:$DDC_SMART_CONTRACT_VERSION)
docker cp $id::/ddc-smart-contract/artifacts/ ./artifacts/
docker rm -v $id
```

## Versioning strategy

The package must follow **Semantic Versioning** (SemVer).
This strategy provides information on the type of changes introduced in a given version, compared to the previous one, in a unified format that automated tools can use.

The version is expressed as **MAJOR.MINOR.PATCH**.

- MAJOR introduces one or more breaking changes.
- MINOR introduces one or more backwards-compatible API changes.
- PATCH only introduces bug fixes with no API changes.

For more information, see "[Semantic Versioning](https://semver.org/)".

|      Increment this value      |                                                                                                                                                                             Under these conditions                                                                                                                                                                             |                                                                                                                               Example                                                                                                                              |
|:------------------------------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|:------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| **MAJOR**                          | There is at least one breaking change in the current repository - a backwards-incompatible change to the API surface (the exposed part of the API) or features in a way that risks compilation or runtime errors.  <br><br>A major version bump in the _upstream_ repository upon syncing a fork.   <br><br>When incrementing the **MAJOR** version, always reset the  **PATCH**  and  **MINOR**  values to `0`. | Versions `2.1.0` and `3.0.0` are incompatible and cannot be used interchangeably without risk.<br><br>_Upstream_ version was incremented from `2.0.1` to `3.0.0` or higher.                                                                                                         |
| **MINOR** (same **MAJOR** value)       | The highest **MINOR** introduces functionality in a backwards-compatible way, which includes:<br>• Changing the API surface or features without risking compilation or runtime errors.<br>• Adding non-API features.  <br><br>A minor version bump in the _upstream_ repository upon syncing a fork.<br><br>**Note**: When incrementing the minor version, always reset the  **PATCH**  version to `0`.        | It is possible to use `2.2.0` to satisfy a dependency on `2.1.0` because `2.2.0` is backwards-compatible. But it is not possible to use version `2.1.0` to satisfy a dependency on `2.2.0`.<br><br>_Upstream_ version was incremented from `2.0.1` to `2.1.0`, but lower than `3.0.0`. |
| **PATCH** (same **MAJOR.MINOR** values) | The highest **PATCH** carries bug fixes without modifying the API at all. The API remains identical, and the features are not changed.<br><br>A patch version bump in the _upstream_ repository upon syncing a fork.                                                                                                                                                                     | Versions `2.2.0` and `2.2.1` should be interchangeable because they have the same API, even though `2.2.1` includes a bug fix not present in `2.2.0`.<br><br>_Upstream_ version was incremented from `2.0.1` to `2.0.2`, but lower than `2.1.0`.                                                                                                                      |

## Development
We use `rustfmt` for the code formatting.
[How to install](https://github.com/rust-lang/rustfmt#on-the-nightly-toolchain)
In order to format code in the specific directory, run:
```
cargo +nightly fmt
```
