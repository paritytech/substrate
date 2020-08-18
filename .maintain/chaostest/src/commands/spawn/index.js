const { Command, flags } = require('@oclif/command')
const Hypervisor = require('../../hypervisor')
const CONFIG = require('../../config')()
const { succeedExit, errorExit } = require('../../utils/exit')
const logger = require('../../utils/logger')

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
      const command = args.chainType
        if (command === 'dev') {
            logger.debug('Starting with dev mode...')
            await hypervisor.createDevNode(options)
        } else if (command === 'local') {
            logger.debug('Starting a network with 2 default validators...')
            await hypervisor.createAliceBobNodes(options)
        } else if (chainspec){
            options = {
                image: image,
                port,
                chainspecFileName: chainspec,
            }
            await hypervisor.createCustomChain(options)
        } else {
            errorExit('A chainspec is required to create customized chain, if not given, try dev or local')
        }
        succeedExit()
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
  chainspec: flags.string({ char: 'c', description: 'number of full nodes, if not set but exists, default to 1' })
}

SpawnCommand.args = [{ name: 'chainType' }]

module.exports = SpawnCommand
