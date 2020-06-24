const k8s = require('@kubernetes/client-node')
const { isFunction } = require('../../utils')
const logger = require('../../utils/logger')

// load k8s
const kc = new k8s.KubeConfig()
kc.loadFromDefault()

// load k8s Apis
const k8sAppApi = kc.makeApiClient(k8s.AppsV1Api)
const k8sCoreApi = kc.makeApiClient(k8s.CoreV1Api)

const createNamespace = async namespace => {
  const namespaceJson = {
    apiVersion: 'v1',
    kind: 'Namespace',
    metadata: {
      name: namespace
    }
  }
  return await k8sCoreApi.createNamespace(namespaceJson)
}

const readNamespace = async namespace => {
  return await k8sCoreApi.readNamespace(namespace)
}

const createPod = async (nodeSpec, namespace) => {
  const { label, nodeId, image, args, port } = nodeSpec
  const spec = {
    metadata: {
      labels: {
        app: label
      },
      name: nodeId
    },
    spec: {
      containers: [
        {
          image: image,
          imagePullPolicy: 'Always',
          name: nodeId,
          ports: [{ containerPort: port }],
          args: args
        }
      ]
    }
  }
  return await k8sCoreApi.createNamespacedPod(namespace, spec)
}

const getDeploymentStatus = async (deploymentName, namespace) => {
  const response = await k8sAppApi.readNamespacedDeploymentStatus(deploymentName, namespace)
  const status = response.response.body.status
  function getAvailability (item) {
    return item.type === 'Available'
  }
  if (status && status.conditions) {
    return status.conditions.find(getAvailability)
  }
  return undefined
}

const deleteNamespace = async (namespace) => {
  logger.debug(`Taking down Namespace ${namespace}...`)
  if (process.env.KEEP_NAMESPACE && process.env.KEEP_NAMESPACE === 1) {
    return
  }
  return k8sCoreApi.deleteNamespace(namespace)
}

const getNamespacedPods = async (namespace) => {
  const response = await k8sCoreApi.listNamespacedPod(namespace)
  return response.body.items
}

const getPod = async (podName, namespace) => {
  const pods = await getNamespacedPods(namespace)
  const found = pods.find(
    (pod) => !!pod.metadata && pod.metadata.name === podName && !!pod.status && pod.status.podIP
  )
  if (!found) {
    throw Error(`GetNode(${podName}): node is not present in the cluster`)
  }
  return found
}

const startForwardServer = async (namespace, pod, port, onReady) => new Promise((resolve, reject) => {
  const net = require('net')
  const forward = new k8s.PortForward(kc)

  // This simple server just forwards traffic from itself to a service running in kubernetes
  // -> localhost:8080 -> port-forward-tunnel -> kubernetes-pod
  // This is basically equivalent to 'kubectl port-forward ...' but in Javascript.
  const server = net.createServer((socket) => {
    forward.portForward(namespace, pod, [port], socket, null, socket)
  })
  // TODO: add Ws proxy server to adopt the polkadot/api
  server.listen(port, '127.0.0.1', (err) => {
    if (err) {
      logger.error('Error starting server')
      reject(err)
    }
    logger.info('Forwarding server started, ready to connect')
    resolve()
    // Optional onReady hook when server started
    if (onReady && isFunction(onReady)) {
      onReady()
    }
  })
})

module.exports = { createNamespace, readNamespace, createPod, deleteNamespace, getDeploymentStatus, getPod, getNamespacedPods, startForwardServer }
