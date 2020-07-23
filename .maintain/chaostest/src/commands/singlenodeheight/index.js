const { Command, flags } = require('@oclif/command')
const CONFIG = require('../../config')()
const { succeedExit, errorExit } = require('../../utils/exit')
const Hypervisor = require('../../hypervisor')
const logger = require('../../utils/logger')

class SingleNodeHeightCommand extends Command {
  async run () {
    const { flags } = this.parse(SingleNodeHeightCommand)
    let port = flags.port
    let url = flags.url
    const wait = flags.wait || 600 * 1000
    const height = flags.height || 10
    const namespace = flags.namespace || CONFIG.namespace
    const pod = flags.pod || (CONFIG.nodes && CONFIG.nodes[0]) ? CONFIG.nodes[0].podName : undefined
    const now = Date.now()

    const hypervisor = new Hypervisor(CONFIG)
    if (!!url && !!port) {
      JsonRpcCallTestHeight(url, port)
    } else if (!!pod && !!namespace) {
      url = 'http://127.0.0.1'
      port = 9933
      await hypervisor.startForwardServer(namespace, pod, port)
      JsonRpcCallTestHeight(url, port)
    } else {
      errorExit('Not enough parameters provided. Either specify url and port or pod and namespace.')
    }

    async function JsonRpcCallTestHeight (url, port) {
      logger.debug('Polling chain height...')
      if (Date.now() < now + wait) {
        try {
          const curHeight = await hypervisor.getChainBlockHeight(url, port)
          logger.debug('Current Block Height: ' + curHeight)
          if (curHeight > height) {
            logger.info(`Single dev node Blockheight reached ${height}`)
            succeedExit()
          } else {
            setTimeout(() => JsonRpcCallTestHeight(url, port), 2000)
          }
        } catch (error) {
          errorExit('Error requesting chain block height', error)
        }
      } else {
        errorExit('Timed out')
      }
    }
  }
}

SingleNodeHeightCommand.description = 'Test if targeted node is producing blocks > certain height'

SingleNodeHeightCommand.flags = {
  port: flags.integer({ char: 'p', description: 'port to deploy' }),
  url: flags.string({ char: 'u', description: 'connect url' }),
  timeout: flags.string({ char: 't', description: 'wait time in miliseconds to halt' }),
  height: flags.string({ char: 'h', description: 'desired height to test' }),
  pod: flags.string({ description: 'desired pod to test' }),
  namespace: flags.string({ description: 'desired namespace to test' })
}

module.exports = SingleNodeHeightCommand
