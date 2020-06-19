const { Command, flags } = require('@oclif/command')
const { succeedExit, errorExit } = require('../../utils/exit')
const logger = require('../../utils/logger')
const Hypervisor = require('../../hypervisor')

class AddCommand extends Command {
  async run () {
    const { flags } = this.parse(SpawnCommand)
    const { args } = this.parse(SpawnCommand)
    const port = flags.port || 9933
    const namespace = flags.namespace || 'substrate-ci'
    const chainspec = flags.chainspec
    const number = flags.number || 1
    const CONFIG = require('../../config')()

    const hypervisor = new Hypervisor(CONFIG)
    let options = {
        number, port
    }
    const config = hypervisor.config
    if (!config.namespace) errorExit('namespace has to be present')
    if (!config.image) errorExit('image has to be present')
    if (!config.bootnode) errorExit('chain has to be spawned first with command: chaostest spawn [flags]')
    try {
      const nodeType = args.nodeType
      if (nodeType === 'validator') {
        logger.debug('Starting with dev mode...')
        await hypervisor.addCustomNode(options)
      } else if (nodeType === 'peer') {
        logger.debug('Starting a network with 2 default validators...')
        await hypervisor.createAliceBobNodes(options)
      } else {
        errorExit('validator or peer only')
      }
    } catch (error) {
      logger.error(error)
      process.exit(1)
    }
  }
}

AddCommand.description = 'Spawn a local testnet with options'

AddCommand.flags = {
//   image: flags.string({ char: 'i', description: 'image to deploy' }),
  port: flags.integer({ char: 'p', description: 'port to deploy on' }),
//   namespace: flags.string({ description: 'desired namespace to deploy to', env: 'NAMESPACE' }),
//   validator: flags.string({ char: 'v', description: 'number of validators' }),
  number: flags.string({ char: 'n', description: 'number of options[validators, peers]' }),
  chainspec: flags.string({ char: 'c', description: 'number of full nodes, if not set but exists, default to 1' })
}

AddCommand.args = [{ name: 'nodeType' }]

module.exports = SpawnCommand
