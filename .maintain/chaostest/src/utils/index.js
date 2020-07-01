const getBootNodeUrl = (bootnode) => {
  return `/dns4/${bootnode.ip}/tcp/30333/p2p/${bootnode.peerId}`
}

const isFunction = (obj) => {
  return !!(obj && obj.constructor && obj.call && obj.apply)
}

const isNodeType = (node, type) => {
  return node.nodeType === type
}

const getNodesFromType = (nodes, type) => {
  return nodes.filter((node) => {
    return isNodeType(node, type)
  })
}

const getChainspec = (chainspec) => {
  if (chainspec === 'dev' || chainspec === 'local') {
    return chainspec
  }
  return `/chaoshelper/${chainspec}`
}

module.exports = { getBootNodeUrl, isFunction, getNodesFromType, getChainspec }
