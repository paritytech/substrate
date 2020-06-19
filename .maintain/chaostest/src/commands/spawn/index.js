const { Command, flags } = require('@oclif/command')
const logger = require('../../utils/logger')
const Hypervisor = require('../../hypervisor')
const CONFIG = require('../../config')()

class SpawnCommand extends Command {
  async run () {
    const { flags } = this.parse(SpawnCommand)
    const { args } = this.parse(SpawnCommand)
    const namespace = flags.namespace || 'substrate-ci'
    const image = flags.image || 'parity/substrate:latest'
    const chainspec = flags.chainspec
    const port = flags.port || 9933

    const hypervisor = new Hypervisor(CONFIG)
    let options = {
        image, port
    }
    try {
      // Check/Create namespace
      await hypervisor.readOrCreateNamespace(namespace)
      const command = args.customCommand
      if (command) {
        if (command === 'dev') {
          logger.debug('Starting with dev mode...')
          await hypervisor.createDevNode(options)
        } else if (command === 'local') {
          logger.debug('Starting a network with 2 default validators...')
          await hypervisor.createAliceBobNodes(options)
        } else {
            const options = {
                image: image,
                port,
                chainSpecFileName: chainspec,
            }
            await hypervisor.createCustomChain(options)
          // TODO: customized chain with chainName
        }
      }
    } catch (error) {
      logger.error(error)
      process.exit(1)
    }
  }
}

SpawnCommand.description = 'Spawn a local testnet with options'

SpawnCommand.flags = {
  image: flags.string({ char: 'i', description: 'image to deploy' }),
  port: flags.integer({ char: 'p', description: 'port to deploy on' }),
  namespace: flags.string({ description: 'desired namespace to deploy to', env: 'NAMESPACE' }),
//   validator: flags.string({ char: 'v', description: 'number of validators' }),
  number: flags.string({ char: 'n', description: 'number of options[validators, peers]' }),
  chainspec: flags.string({ char: 'c', description: 'number of full nodes, if not set but exists, default to 1' })
}

SpawnCommand.args = [{ name: 'customCommand' }]

module.exports = SpawnCommand
