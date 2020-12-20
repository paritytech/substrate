const { Command, flags } = require('@oclif/command')
const CONFIG = require('../../config')()
const logger = require('../../utils/logger')
const Hypervisor = require('../../hypervisor')

class CleanCommand extends Command {
  async run () {
    const { flags } = this.parse(CleanCommand)
    const namespace = flags.namespace || CONFIG.namespace
    const hypervisor = new Hypervisor(CONFIG)
    // Delete corresponding namespace, default to CONFIG.namespace
    try {
      if (namespace) {
        await hypervisor.cleanup(namespace)
      } else {
        logger.debug('Nothing to clean up')
      }
    } catch (error) {
      logger.error(error)
      process.exit(1)
    }
  }
}

CleanCommand.description = 'Clean up resources based on namespace'

CleanCommand.flags = {
  namespace: flags.string({ char: 'n', description: 'desired namespace to clean up', env: 'NAMESPACE' })
}

module.exports = CleanCommand
