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

module.exports = { getApi, getChainBlockHeight }
