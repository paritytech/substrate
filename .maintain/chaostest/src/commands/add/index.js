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
    // const label = flags.label
    

    const hypervisor = new Hypervisor(CONFIG)
    const config = hypervisor.config
    console.log(CONFIG)
    if (!config.namespace) errorExit('namespace has to be present')
    if (!config.image) errorExit('image has to be present')
    if (!config.bootnode) errorExit('chain has to be spawned first with command: chaostest spawn [flags]')
    try {
      const nodeType = args.nodeType
      if (nodeType === 'validator' || nodeType === 'peer') {
        logger.debug('Adding nodes to current network...')
        let options = {
            number, port, nodeType
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

AddCommand.description = 'Spawn a local testnet with options'

AddCommand.flags = {
//   image: flags.string({ char: 'i', description: 'image to deploy' }),
  port: flags.integer({ char: 'p', description: 'port to deploy on' }),
//   namespace: flags.string({ description: 'desired namespace to deploy to', env: 'NAMESPACE' }),
//   validator: flags.string({ char: 'v', description: 'number of validators' }),
//   label: flags.string({ char: 'l', description: 'label to mark the nodes'}),
  number: flags.string({ char: 'n', description: 'number of options[validators, peers]' }),
  chainspec: flags.string({ char: 'c', description: 'number of full nodes, if not set but exists, default to 1' })
}

AddCommand.args = [{ name: 'nodeType' }]

module.exports = AddCommand
