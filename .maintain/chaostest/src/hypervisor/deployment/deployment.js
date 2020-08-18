const k8s = require('../modules/k8s')
const { pollUntil } = require('../../utils/wait')
const { getBootNodeUrl, getNodesFromType, getChainspec } = require('../../utils')
const logger = require('../../utils/logger')
const { getKeyFromNodeId } = require('../modules/keyring')

exports.readOrCreateNamespace = async function (namespace) {
  try {
    logger.debug('Reading namespace')
    await k8s.readNamespace(namespace) // if namespace is available, do not create here
  } catch (error) {
    if (error.response.statusCode !== 404) {
      logger.error(error)
      throw error
    }
    logger.debug('Namespace not present, creating...')
    await k8s.createNamespace(namespace)
  }
  this.config.setNamespace(namespace)
}
exports.createAlice = async function (image, port) {
  const substrateArgs = [
    '--chain',
    'local',
    '--node-key',
    '0000000000000000000000000000000000000000000000000000000000000001',
    '--validator',
    '--no-telemetry',
    '--rpc-cors',
    'all',
    '--prometheus-external',
    '--alice']
  const nodeSpec = {
    nodeId: 'alice',
    image,
    port,
    args: substrateArgs,
    chainspec: 'local'
  }
  nodeSpec.extraInfo = {
    nodeType: 'bootnode',
    chainspec: 'local',
    peerId: '12D3KooWEyoppNCUx8Yx66oV9fJnriXwCcXwDDUA2kj6vnc6iDEp',
    image
  }
  await this.createNode(nodeSpec)
}

exports.createBob = async function (image, port) {
  const substrateArgs = [
    '--chain',
    'local',
    '--node-key',
    '0000000000000000000000000000000000000000000000000000000000000002',
    '--validator',
    '--bob',
    '--no-telemetry',
    '--rpc-cors',
    'all',
    '--prometheus-external',
    '--bootnodes',
    getBootNodeUrl(this.config.bootnode)]
  const nodeSpec = {
    nodeId: 'bob',
    image,
    port,
    args: substrateArgs
  }
  nodeSpec.extraInfo = {
    nodeType: 'validator'
  }
  await this.createNode(nodeSpec)
}

exports.createAliceBobNodes = async function (options) {
    const {image, port} = options
  await this.createAlice(image, port)
  await this.createBob(image, port)
}

exports.createDevNode = async function (options) {
    const {image, port} = options
  const substrateArgs = [
    '--dev',
    '--node-key',
    '0000000000000000000000000000000000000000000000000000000000000001',
    '--rpc-external',
    '--ws-external']
  const nodeSpec = {
    nodeId: 'node-validator-0',
    image,
    port,
    args: substrateArgs
  }
  nodeSpec.extraInfo = {
    nodeType: 'bootnode',
    chainspec: 'dev',
    image
  }
  await this.createNode(nodeSpec)
}

exports.createBootNode = async function(options) {
    const substrateArgs = [
        '--chain',
        options.chainspec,
        // 'local',
        '--node-key',
        '0000000000000000000000000000000000000000000000000000000000000001',
        '--validator',
        '--no-telemetry',
        '--rpc-cors',
        'all',
        '-d',
        '/substrate',
        '--unsafe-ws-external',
        '--unsafe-rpc-external',
        '--prometheus-external',
    ]

    const nodeSpec = {
        nodeId: 'bootnode',
        image: options.image,
        port: options.port,
        args: substrateArgs,
        customChainspec: options.customChainspec,
        extraInfo: {
            nodeType: 'bootnode',
            chainspec: options.chainspecFileName,
            image: options.image
          }
      }
    await this.createNode(nodeSpec)
}

exports.createCustomNode = async function(options, nodeId) {
    const substrateArgs = [
        '--chain',
        getChainspec(options.chainspec),
        '--no-telemetry',
        '--rpc-cors',
        'all',
        '--node-key',
        getKeyFromNodeId(nodeId),
        '-d',
        '/substrate',
        '--unsafe-ws-external',
        '--unsafe-rpc-external',
        '--prometheus-external',
        '--bootnodes',
        getBootNodeUrl(this.config.bootnode)
    ]
    if (options.nodeType === 'validator') {
        substrateArgs.push('--validator')
    }
    const nodeSpec = {
        nodeId: nodeId,
        image: options.image,
        port: options.port,
        args: substrateArgs,
        extraInfo: {
            nodeType: options.nodeType,
        }
    }
    await this.createNode(nodeSpec)
}

exports.createCustomChain = async function (options) {
    options.customChainspec = true
    options.chainspec = getChainspec(options.chainspecFileName)
    await this.createBootNode(options)
}

exports.addCustomNodes = async function (options) {
    const {number, port, nodeType, name} = options
    const nodeOption = {image: this.config.bootnode.image, port, chainspec: this.config.bootnode.chainspec, nodeType}
    if (name) {
        await this.createCustomNode(nodeOption, name)
    } else {
        const nodeIdPrefix = `node-${nodeType}-`
        const deployedNodes = getNodesFromType(this.config.nodes, options.nodeType)
        const deployArray = []
        for(let i=1; i <= number; i++) {
            const nodeIdPostfix = deployedNodes.length + i
            deployArray.push(this.createCustomNode(nodeOption, nodeIdPrefix+nodeIdPostfix))
        }
        await Promise.all(deployArray)
    }
}

exports.createNode = async function (nodeSpec) {
  logger.info(`Creating ${nodeSpec.nodeId} as ${nodeSpec.extraInfo ? nodeSpec.extraInfo.nodeType : 'peer'} in ${this.config.namespace}`)
  await k8s.createPod(nodeSpec, this.config.namespace)
  logger.debug('Polling pod status')
  const pod = await pollUntil(
    () => k8s.getPod(nodeSpec.nodeId, this.config.namespace)
  )
  const nodeInfo = {
    podName: nodeSpec.nodeId,
    ip: pod.status.podIP,
    port: nodeSpec.port
  }
  if (nodeSpec.extraInfo) {
    if (nodeSpec.extraInfo.nodeType === 'bootnode') {
      await this.startForwardServer(this.config.namespace, nodeSpec.nodeId, nodeSpec.port)
      nodeSpec.extraInfo.peerId = await this.getPeerId('http://127.0.0.1', 9933)
    }
    Object.assign(nodeInfo, nodeSpec.extraInfo)
  }
  logger.info(`${nodeSpec.nodeId} is created`)
  this.config.addNode(nodeInfo)
  return
}

exports.cleanup = async function (namespace) {
  await k8s.deleteNamespace(namespace)
  if (namespace === this.config.namespace) {
    this.config.reset()
  }
}

exports.getPodInfoInConfig = function (namespace, podName) {
  if (this.config.namespace === namespace && Array.isArray(this.config.nodes)) {
    return this.config.nodes.find((node) => node.podName === podName)
  } else {
    throw Error('No pod present in the namespace in config')
  }
}

exports.startForwardServer = async function (namespace, pod, port, onReady) {
  await k8s.startForwardServer(namespace, pod, port, onReady)
}
