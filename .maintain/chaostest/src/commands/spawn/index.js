const { Command, flags } = require('@oclif/command')
const logger = require('../../utils/logger')
const Hypervisor = require('../../hypervisor')
const CONFIG = require('../../config')()

class SpawnCommand extends Command {
  async run () {
    const { flags } = this.parse(SpawnCommand)
    const { args } = this.parse(SpawnCommand)
    const imageTag = flags.image || 'parity/substrate:latest'
    const port = flags.port || 9933
    const namespace = flags.namespace || 'substrate-ci'
    const validator = flags.validator || 0
    const node = flags.node || 1

    const hypervisor = new Hypervisor(CONFIG)
    try {
      // Check/Create namespace
      await hypervisor.readOrCreateNamespace(namespace)
      const chainName = args.chainName
      if (chainName) {
        if (chainName === 'dev') {
          logger.debug('Starting a fullnode in dev mode...')
          await hypervisor.createDevNode(imageTag, port)
        } else if (chainName === 'alicebob') {
          await hypervisor.createAliceBobNodes(imageTag, port)
        } else {
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
  validator: flags.string({ char: 'v', description: 'number of validators' }),
  node: flags.string({ char: 'n', description: 'number of full nodes, if not set but exists, default to 1' }),
  key: flags.string({ char: 'k', description: 'number of full nodes, if not set but exists, default to 1' }),
  chainspec: flags.string({ char: 'c', description: 'number of full nodes, if not set but exists, default to 1' })
}

SpawnCommand.args = [{ name: 'chainName' }]

module.exports = SpawnCommand
