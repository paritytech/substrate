const { ApiPromise, WsProvider } = require('@polkadot/api')
const { HttpProvider } = require('@polkadot/rpc-provider')

const getApi = async (url) => {
  const httpProvider = new HttpProvider(url)
  return httpProvider
  //   const api = await ApiPromise.create({ provider: wsProvider })
  //   return api
  // TODO: tried to use websocket provider here, but the polkadot/api version is not stable yet, using http provider for now
}

const getChainBlockHeight = async (provider) => {
  const data = await provider.send('chain_getBlock', [])
  const height = parseInt(data.block.header.number, 16)
  return height
}

const insertKey = async (provider, key) => {
  const data = await provider.send('author_insertKey', [key.type, key.mnemonic, key.public])
  console.log(data)
}

const getPeerId = async (provider) => {
  const data = await provider.send('system_localPeerId', [])
  return data
}


module.exports = { getApi, getChainBlockHeight, getPeerId }

