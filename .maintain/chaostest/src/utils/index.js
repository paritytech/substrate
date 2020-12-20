const getBootNodeUrl = (bootnode) => {
  return `/dns4/${bootnode.ip}/tcp/30333/p2p/${bootnode.peerId}`
}

const isFunction = (obj) => {
  return !!(obj && obj.constructor && obj.call && obj.apply)
}

module.exports = { getBootNodeUrl, isFunction }
