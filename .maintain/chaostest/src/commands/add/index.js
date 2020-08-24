const { Command, flags } = require('@oclif/command')
const { succeedExit, errorExit } = require('../../utils/exit')
const logger = require('../../utils/logger')
const Hypervisor = require('../../hypervisor')
const CONFIG = require('../../config')()

class AddCommand extends Command {
  async run () {
    const { flags } = this.parse(AddCommand)
    const { args } = this.parse(AddCommand)
    const port = flags.port || 9933
    const chainspec = flags.chainspec
    const number = flags.number || 1
    const name = flags.name    

    const hypervisor = new Hypervisor(CONFIG)
    const config = hypervisor.config
    // Checking if there is a current deployment
    if (!config.namespace) errorExit('namespace has to be present')
    if (!config.bootnode) errorExit('chain has to be spawned first with command: chaostest spawn [flags]')
    if (!config.bootnode.image) errorExit('image has to be present')
    try {
      const nodeType = args.nodeType
      if (nodeType === 'validator' || nodeType === 'peer') {
        logger.debug('Adding nodes to current network...')
        let options = {
            number, port, nodeType, name
            }
        await hypervisor.addCustomNodes(options)
      } else {
        errorExit('Validator or peer only')
      }
    } catch (error) {
      logger.error(error)
      errorExit(error)
    }
  }
}

AddCommand.description = 'Add nodes to a spawned testnet'

AddCommand.flags = {
  port: flags.integer({ char: 'p', description: 'port to deploy on' }),
  name: flags.string({ description: 'node name to specify (also this is used as the seed for the node's key)' }),
  number: flags.string({ char: 'n', description: 'number of nodes to deploy (default to 1 if not specified or a node name is given)' }),
  chainspec: flags.string({ char: 'c', description: 'specify a chainspec to use to deploy' })
}

AddCommand.args = [{ name: 'nodeType' }]

module.exports = AddCommand
