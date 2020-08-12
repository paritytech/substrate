chaostest
=========

A cli for chaos testing on substrate

[![oclif](https://img.shields.io/badge/cli-oclif-brightgreen.svg)](https://oclif.io)
[![Version](https://img.shields.io/npm/v/chaostest.svg)](https://npmjs.org/package/chaostest)
[![Downloads/week](https://img.shields.io/npm/dw/chaostest.svg)](https://npmjs.org/package/chaostest)

<!-- toc -->
* [Usage](#usage)
* [Commands](#commands)
<!-- tocstop -->
# Usage
<!-- usage -->
```sh-session
$ npm install -g chaostest // yarn add global chaostest
$ chaostest COMMAND
running command...
$ chaostest (-v|--version|version)
chaostest/0.0.0 darwin-x64 node-v8.16.0
$ chaostest --help [COMMAND]
USAGE
  $ chaostest COMMAND
...
```
<!-- usagestop -->
# Commands
<!-- commands -->
* [`chaostest spawn`](#chaostest-spawn)
* [`chaostest singlenodeheight`](#chaostest-singlenodeheight)
* [`chaostest clean`](#chaostest-clean)

## `chaostest spawn`

Spawn a testnet based on your local k8s configuration. Could be either a dev node, a two node alicebob chain or a customized chain with various validators/fullnodes.

```
USAGE
  $ chaostest spawn [ARGUMENTS] [FLAGS]

Arguments
  dev,  a single fullnode in --dev mode
  alicebob, a two nodes private chain with Alice as bootnode and Bob as validator
  [chainName], a customized chain deployed with -v numbers of validators and -n numbers of fullnodes

Flags
  --image, -i, the image tag of the certain substrate version you want to deploy
  --port, -p, the port to expose when image is deployed in a pod
  --namespace, the desired namespace to deploy on
  --validator, -v, the number of substrate validators to deploy
  --node, -n, the number of full nodes, if not set but exists, default to 1
  
DESCRIPTION
  ...
  Extra documentation goes here
```

_See code: [src/commands/spawn/index.js](https://github.com/paritytech/substrate/blob/harry/chaostest-init/.maintain/chaostest/src/commands/spawn/index.js)_

## `chaostest singlenodeheight`

Test against a fullnode on --dev mode to check if it can successfully produce blocks to a certain height.

```
USAGE
  $ chaostest singlenodeheight [FLAGS]

FLAGS
  -h , the desired height of blocks to check if reachable, this only works with integers smaller than 2^6 
  -t, the wait time out before it halts the polling
```

_See code: [src/commands/singlenodeheight/index.js](https://github.com/paritytech/substrate/blob/harry/chaostest-init/.maintain/chaostest/src/commands/singlenodeheight/index.js)_

## `chaostest clean`

Clean up the k8s deployment by namespace.

```
USAGE
  $ chaostest clean [FLAGS]

FLAGS
  -n , the desired namespace to delete on your k8s cluster
```

_See code: [src/commands/clean/index.js](https://github.com/paritytech/substrate/blob/harry/chaostest-init/.maintain/chaostest/src/commands/clean/index.js)_
<!-- commandsstop -->
