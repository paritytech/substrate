const k8s = require('../modules/k8s')
const { pollUntil } = require('../../utils/wait')
const { getBootNodeUrl } = require('../../utils')
const logger = require('../../utils/logger')

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
    '--chain=local',
    '--node-key',
    '0000000000000000000000000000000000000000000000000000000000000001',
    '--validator',
    '--no-telemetry',
    '--rpc-cors',
    'all',
    '--alice']
  const nodeSpec = {
    nodeId: 'alice',
    image,
    port,
    args: substrateArgs
  }
  nodeSpec.extraInfo = {
    nodeType: 'bootnode',
    privateKey: '',
    publicKey: '',
    peerId: '12D3KooWEyoppNCUx8Yx66oV9fJnriXwCcXwDDUA2kj6vnc6iDEp'
  }
  await this.createNode(nodeSpec)
}

exports.createBob = async function (image, port) {
  const substrateArgs = [
    '--chain=local',
    '--node-key',
    '0000000000000000000000000000000000000000000000000000000000000002',
    '--validator',
    '--bob',
    '--no-telemetry',
    '--rpc-cors',
    'all',
    '--bootnodes',
    getBootNodeUrl(this.config.bootnode)]
  const nodeSpec = {
    nodeId: 'bob',
    image,
    port,
    args: substrateArgs
  }
  nodeSpec.extraInfo = {
    nodeType: 'validator',
    privateKey: '',
    publicKey: ''
  }
  await this.createNode(nodeSpec)
}

exports.createAliceBobNodes = async function (image, port) {
  await this.createAlice(image, port)
  await this.createBob(image, port)
}

exports.createDevNode = async function (image, port) {
  const substrateArgs = ['--dev', '--rpc-external', '--ws-external']
  const nodeSpec = {
    nodeId: 'node-1',
    image,
    port,
    args: substrateArgs
  }
  await this.createNode(nodeSpec)
}

exports.createNode = async function (nodeSpec) {
  logger.info(`Creating ${nodeSpec.nodeId} as ${nodeSpec.extraInfo ? nodeSpec.extraInfo.nodeType : 'FullNode'} in ${this.config.namespace}`)
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
    Object.assign(nodeInfo, nodeSpec.extraInfo)
  }
  logger.info(`${nodeSpec.nodeId} is created`)
  this.config.addNode(nodeInfo)
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
