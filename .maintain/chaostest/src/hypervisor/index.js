const CONFIG = require('../config')()

function Hypervisor (config) {
  this.config = config || CONFIG
}

// Mount sub modules of the Hypervisor class
require('./deployment')(Hypervisor)
require('./chainApi')(Hypervisor)

module.exports = Hypervisor
