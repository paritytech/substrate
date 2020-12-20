const chainApi = require('../modules/chainApi')

exports.getApi = async function (endpoint) {
  if (this._apiInstance && this._apiInstance.endpoint === endpoint) {
    return this._apiInstance.instance
  } else {
    const instance = await chainApi.getApi(endpoint)
    this._apiInstance = { endpoint, instance }
    return instance
  }
}

exports.getChainBlockHeight = async function (url, port) {
  const api = await this.getApi(url + ':' + port)
  return chainApi.getChainBlockHeight(api)
}
