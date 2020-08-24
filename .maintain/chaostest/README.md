chaostest
=========

A cli for chaos testing on substrate

[![oclif](https://img.shields.io/badge/cli-oclif-brightgreen.svg)](https://oclif.io)
[![Version](https://img.shields.io/npm/v/chaostest.svg)](https://npmjs.org/package/chaostest)
[![Downloads/week](https://img.shields.io/npm/dw/chaostest.svg)](https://npmjs.org/package/chaostest)

<!-- toc -->
* [Setup](#setup)
* [Usage](#usage)
* [Commands](#commands)
<!-- tocstop -->

# Setup
<!-- setup -->
To use this CLI tool.
You need: 
```
kubectl cli [installed and connected to a cluster](https://cloud.google.com/kubernetes-engine/docs/how-to/cluster-access-for-kubectl)
node js 8+ [installed](https://nodesource.com/blog/installing-node-js-tutorial-using-nvm-on-mac-os-x-and-ubuntu/)
```
https://cloud.google.com/kubernetes-engine/docs/how-to/cluster-access-for-kubectl
<!-- setupstop -->
# Usage
<!-- usage -->
```sh-session
$ npm install -g chaostest // yarn add global chaostest
OR
$ npm link

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
* [`chaostest add`](#chaostest-add)
* [`chaostest clean`](#chaostest-clean)
* [`chaostest singlenodeheight`](#chaostest-singlenodeheight)


## `chaostest spawn`

Spawn a testnet based on your local k8s configuration. Could be either a dev node, a two node alicebob chain or a customized chain with various validators/fullnodes.

Namespace is essential here (default to ```substrate-ci```)
It is recommended to set your own namespace as an environment variable BEFORE running ```chaostest spawn``` to not conflict with others:
```
export NAMESPACE=YOUR_OWN_NAMESPACE (ex: harry-chaos-test)
```

```
USAGE
  $ chaostest spawn [ARGUMENTS] [FLAGS]

Arguments
  dev,  a single fullnode in --dev mode
  local, a two nodes private chain with Alice as bootnode and Bob as validator
  [chainName], a customized chain deployed with -c as a customized chainspec. (currently using pre-configured chainspecs to test on)

Flags
  --image, -i, the image tag of the certain substrate version you want to deploy
  --port, -p, the port to expose when image is deployed in a pod
  --namespace, the desired namespace to deploy on
  --chainspec, -c, the desired chainspec to pass as argument on bootstrapping a private network
  
DESCRIPTION
  ...
  Extra documentation goes here
```

_See code: [src/commands/spawn/index.js](https://github.com/paritytech/substrate/blob/harry/chaostest-init/.maintain/chaostest/src/commands/spawn/index.js)_

## `chaostest add`

Add various numbers of validator / peer nodes to the network. Only use after you spawned the network.

```
USAGE
  $ chaostest add [ARGUMENTS] [FLAGS]

Arguments
  validator, the nodes will be deployed to the network with --validator and key will be based on the node-name (if not specified, it would be "node-validator-XX")
  peer, the nodes will be deployed to the network as fullnodes and key will be based on the node-name (if not specified, it would be "node-peer-XX")

Flags
  --number, -n, number of nodes to deploy (default to 1 if not specified or a node name is given)
  --port, -p, port to deploy on
  --name, node name to specify (also this would be the seed of the node)
  
DESCRIPTION
  ...
  Extra documentation goes here
```

_See code: [src/commands/add/index.js](https://github.com/paritytech/substrate/blob/harry/chaostest-init/.maintain/chaostest/src/commands/add/index.js)_


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
