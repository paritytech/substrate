const CONFIG = require('../config')()

// Mount an instance of configuration or a new instance from config
// TODO: extend this to namespace based configuration
function Hypervisor (config) {
  this.config = config || CONFIG
}

// Mount sub modules of the Hypervisor class
require('./deployment')(Hypervisor)
require('./chainApi')(Hypervisor)

module.exports = Hypervisor
